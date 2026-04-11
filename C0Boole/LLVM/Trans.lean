import C0Boole.Ast
import C0Boole.LLVM.Tree
import C0Boole.Utils.Label
import C0Boole.Utils.Temp

import Std.Data.HashMap

namespace C0Boole.LLVM.Tree.Trans
open C0Boole.Ast
open C0Boole.LLVM.Tree
open C0Boole.Utils.Label
open C0Boole.Utils.Temp

abbrev TempEnv := Std.HashMap String Temp

-- TODO: consider wrapping env meta things into here
structure Env where
  tempEnv : TempEnv
  tc : TempCounter
  lc : LabelCounter

def translateBinOp (op: Ast.BinOp) : Tree.BinOp :=
  match op with
  | .plus => .plus
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .mod => .mod
  | .lt => .lt
  | .lte => .lte
  | .gt => .gt
  | .gte => .gte
  | .eq => .eq
  | .neq => .neq
  | .bitAnd => .bitAnd
  | .xor => .xor
  | .bitOr => .bitOr
  | .shl => .shl
  | .shr => .shr

  | .land => panic! "[Error] land (&&) should have been elaborated away but found in translate_binop"
  | .lor => panic! "[Error] lor (||) should have been elaborated away but found in translate_binop"

partial def translateExpr
  (mexpr : Ast.MarkedExpr)
  (env : Std.HashMap String Temp)
  (tc : TempCounter)
  (lc : LabelCounter)
  : List Tree.Command × Tree.Expr × TempEnv × TempCounter × LabelCounter :=
  match mexpr.node with
  | .var name =>
    match env.get? name with
    | some temp => ([], .temp temp, env, tc, lc)
    | _ =>
      let (temp, tc') := Temp.bumpAndCreate tc
      ([], .temp temp, env.insert name temp, tc', lc)

  | .intLit val => ([], .const val, env, tc, lc)

  | .binop op lhs rhs =>
    let (tempRes, tc') := Temp.bumpAndCreate tc
    let (cmdsLhs, transLhs, env', tc'', lc') := translateExpr lhs env tc' lc
    let (cmdsRhs, transRhs, env'', tc''', lc'') := translateExpr rhs env' tc'' lc'

    (cmdsLhs ++ cmdsRhs ++ [.move tempRes (.binop (translateBinOp op) transLhs transRhs)]
    , .temp tempRes
    , env''
    , tc'''
    , lc'')

  -- TODO: we can consider having a new type for Elaborated AST, which would remove this case
  | .unop _ _ => panic! "[Error] unops should have been elaborated away but found in translateExpr"


  -- TODO: LLVM supports select. is this really something we want to elaborate?
  | .ternary test thenVal elseVal =>
    let (tempRes, tc') := Temp.bumpAndCreate tc
    let (cmdsTest, transTest, env', tc'', lc') := translateExpr test env tc' lc
    let (labelThen, lc'') := Label.bumpAndCreate lc'
    let (labelElse, lc''') := Label.bumpAndCreate lc''

    let (cmdsThen, transThen, env'', tc''', lc''') := translateExpr thenVal env' tc'' lc'''
    let (cmdsElse, transElse, env''', tc'''', lc'''') := translateExpr elseVal env'' tc''' lc'''

    (cmdsTest
    ++ [.ite transTest labelThen labelElse]
    ++ [.label labelThen]
    ++ cmdsThen
    ++ [.move tempRes transThen]
    ++ [.label labelElse]
    ++ cmdsElse
    ++ [.move tempRes transElse]

    , .temp tempRes
    , env'''
    , tc''''
    , lc''''
    )

  | .trueLit => ([], .const 1, env, tc, lc)
  | .falseLit => ([], .const 0, env, tc, lc)

  -- TODO: fix this. definitely not the correct handling of chars
  | .charLit c => ([], .const (Int32.ofNat c.toNat), env, tc, lc)

  | .call fname args =>
    let (argCmds, argExps, env', tc', lc') := List.foldr
      (λ arg (cmdsAcc, expsAcc, envAcc, tcAcc, lcAcc) =>
        let (cmds, exp, env'', tc''', lc'') := translateExpr arg envAcc tcAcc lcAcc
        (cmds ++ cmdsAcc, exp :: expsAcc, env'', tc''', lc'')
      )
      ([], [], env, tc, lc)
      args
    let (tempRes, tc'') := Temp.bumpAndCreate tc'
    (argCmds ++ [.move tempRes (.call fname argExps)], .temp tempRes, env', tc'', lc')

  -- TODO
  | .length _ => ([], .const 0, env, tc, lc)
  | .result => ([], .const 0, env, tc, lc)
  | .hastag => ([], .const 0, env, tc, lc)
  | .stringLit _ => ([], .const 0, env, tc, lc)

partial def translateStm
  (mstm : Ast.MarkedStm)
  (env : Std.HashMap String Temp)
  (tc : TempCounter)
  (lc : LabelCounter)
  : List Tree.Command × TempEnv × TempCounter × LabelCounter :=
  match mstm.node with
  | .assign varName val =>
    let (cmds, expr, env', tc', lc') := translateExpr val env tc lc
    match env.get? varName with
    | some temp =>
      -- dbg_trace s!"Found in env. Assigning {varName} to {temp.name}"
      (cmds ++ [.move temp expr], env', tc', lc')
    | none =>
      -- dbg_trace s!"Couldn't find in env. Creating new temp for {varName}"
      let (temp, tc') := Temp.bumpAndCreate tc
      (cmds ++ [.move temp expr], env', tc', lc')

  | .ifLit test thenBranch elseBranch =>
    let (cmdsTest, transTest, env', tc', lc') := translateExpr test env tc lc
    let (cmdsThen, env'', tc'', lc'') := translateStm thenBranch env' tc' lc'
    let (cmdsElse, env''', tc''', lc''') := translateStm elseBranch env'' tc'' lc''

    let (labelThen, lc'''') := Label.bumpAndCreate lc'''
    let (labelElse, lc''''') := Label.bumpAndCreate lc''''

    (cmdsTest
    ++ [.ite transTest labelThen labelElse]
    ++ [.label labelThen]
    ++ cmdsThen
    ++ [.label labelElse]
    ++ cmdsElse
    , env'''
    , tc'''
    , lc'''''
    )

  | .whileLit test body =>
    let (cmdsTest, transTest, env', tc', lc') := translateExpr test env tc lc
    let (cmdsBody, env'', tc'', lc'') := translateStm body env' tc' lc'

    let (labelGuard, lc''') := Label.bumpAndCreate lc''
    let (labelBody, lc'''') := Label.bumpAndCreate lc'''
    let (labelDone, lc''''') := Label.bumpAndCreate lc''''

    ([ .goto labelGuard
       , .label labelGuard
       ]
    ++ cmdsTest
    ++ [ .ite transTest labelBody labelDone
       , .label labelBody]
    ++ cmdsBody
    ++ [ .goto labelGuard
       , .label labelDone
       ]
    , env''
    , tc''
    , lc''''')

  | .ret valOpt =>
    match valOpt with
    | some retVal =>
      let (cmdsRetVal, transRetVal, env', tc', lc') := translateExpr retVal env tc lc
      (cmdsRetVal ++ [.ret (some transRetVal)], env', tc', lc')
    | none => ([.ret none], env, tc, lc)


  | .seq first rest =>
    let (cmdsFirst, env', tc', lc') := translateStm first env tc lc
    let (cmdsRest, env'', tc'', lc'') := translateStm rest env' tc' lc'

    (cmdsFirst ++ cmdsRest
    , env''
    , tc''
    , lc'')

  -- TODO: weave in type info into TempEnv
  | .declare varName _ value =>
    let (temp, tc') := Temp.bumpAndCreate tc
    let (cmdsValue, env', tc'', lc') := translateStm value (env.insert varName temp) tc' lc
    (cmdsValue, env'.insert varName temp, tc'', lc')

  | .defn varName _ =>
    -- dbg_trace s!"Found a defn. Inserting into env for {varName}"
    let (temp, tc') := Temp.bumpAndCreate tc
    ([], env.insert varName temp, tc', lc)

  | .asop _ _ _ => panic! "[Error] asops should have been elaborated away but found in translateStm"
  | .forLit _ _ _ _ => panic! "[Error] for should have been elaborated away but found in translateStm"

  | .expr mexpr =>
    let (cmds, _, env', tc', lc') := translateExpr mexpr env tc lc
    (cmds, env', tc', lc')

  | .nop => ([], env, tc, lc)

  -- TODO
  | .assert _ => panic! "[Error] unimplemented (assert)"
  | .error _ => panic! "[Error] unimplemented (error)"
  | .annotation _ => panic! "[Error] unimplemented (annotation)"

def translateTau : Ast.Tau → Tree.Tau
  | .int | .char | .bool => .int
  | .string => panic! "[Error] strings are not yet handled"
  | .void => .void

def translateParam (param : Ast.Param) : Tree.Arg :=
  let (tau, name) := param

  -- TODO: make this cleaner. why are we creating temp from name? seems dangerous
  (translateTau tau, Temp.fromName name)

def translateGdecl (gdecl : Ast.GDecl) : Tree.FunctionDef :=
  match gdecl with
  | .fdecl _ _ _ _ => panic! "[Error] fdecls should have been elaborated away but found in translateGdecl"
  | .typedef _ _ => panic! "[Error] typedefs should have been elaborated away but found in translateGdecl"
  | .fdefn retType fname params body _ =>
    let (temps, tc) := Temp.bumpAndCreateK 0 params.length
    let paramsTemps := List.zip params temps
    let (params', seededEnv) := List.foldr
      -- TODO: i don't really like this, since it assumes that in the downstream pass, function args will preserve temp.name and also
      -- explicitly emit %temp.name
      (λ ((tau, varName), temp) (paramsAcc, envAcc) => ((translateTau tau, temp)::paramsAcc, envAcc.insert varName temp))
      ([], {})
      paramsTemps

    -- dbg_trace s!"{seededEnv.contains "n"}"

    let (cmds, _, _, _) := (List.foldl
      (λ (cmdsAcc, envAcc, tcAcc, lcAcc) mstm =>
        let (cmds, env', tc', lc') := translateStm mstm envAcc tcAcc lcAcc
        (cmdsAcc ++ cmds, env', tc', lc')
      )
      ([], seededEnv, tc, 0)
      body)
    ( fname
    , translateTau retType
    , params'
    , cmds)

def translate (program : Ast.Program) : Tree.Program :=
  -- dbg_trace s!"{Ast.Print.ppProgramRaw program}"
  List.map translateGdecl program

end C0Boole.LLVM.Tree.Trans
