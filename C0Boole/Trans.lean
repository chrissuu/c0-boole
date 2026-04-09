import C0Boole.Ast
import C0Boole.Tree
import C0Boole.Utils.Label
import C0Boole.Utils.Temp

import Std.Data.HashMap

namespace C0Boole.Tree.Trans
open C0Boole.Ast
open C0Boole.Tree
open C0Boole.Utils.Label
open C0Boole.Utils.Temp

abbrev TempEnv := Std.HashMap String Temp

-- TODO: consider wrapping env meta things into here
structure Env where
  tempEnv : TempEnv
  tc : TempCounter
  lc : LabelCounter

def translate_binop (op: Ast.BinOp) : Tree.BinOp :=
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
  | .land => .land
  | .lor => .lor
  | .bitAnd => .bitAnd
  | .xor => .xor
  | .bitOr => .bitOr
  | .shl => .shl
  | .shr => .shr

partial def translate_expr
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
    let (cmdsLhs, transLhs, env', tc'', lc') := translate_expr lhs env tc' lc
    let (cmdsRhs, transRhs, env'', tc''', lc'') := translate_expr rhs env' tc'' lc'

    (cmdsLhs ++ cmdsRhs ++ [.move tempRes (.binop (translate_binop op) transLhs transRhs)]
    , .temp tempRes
    , env''
    , tc'''
    , lc'')

  -- TODO: we can consider having a new type for Elaborated AST, which would remove this case
  | .unop _ _ => panic! "[Error] unops should have been elaborated away but found in translate_expr"

  | .ternary test thenBranch elseBranch =>
    let (tempRes, tc') := Temp.bumpAndCreate tc
    let (cmdsTest, transTest, env', tc'', lc') := translate_expr test env tc' lc
    let (labelThen, lc'') := Label.bumpAndCreate lc'
    let (labelElse, lc''') := Label.bumpAndCreate lc''

    let (cmdsThen, transThen, env'', tc''', lc''') := translate_expr thenBranch env' tc'' lc'''
    let (cmdsElse, transElse, env''', tc'''', lc'''') := translate_expr elseBranch env'' tc''' lc'''

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
        let (cmds, exp, env'', tc''', lc'') := translate_expr arg envAcc tcAcc lcAcc
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

partial def translate_stm
  (mstm : Ast.MarkedStm)
  (env : Std.HashMap String Temp)
  (tc : TempCounter)
  (lc : LabelCounter)
  : List Tree.Command × TempEnv × TempCounter × LabelCounter :=
  match mstm.node with
  | .assign varName val =>
    let (cmds, expr, env', tc', lc') := translate_expr val env tc lc
    match env.get? varName with
    | some temp => (cmds ++ [.move temp expr], env', tc', lc')
    | none =>
      let (temp, tc') := Temp.bumpAndCreate tc
      (cmds ++ [.move temp expr], env', tc', lc')

  | .ifLit test thenBranch elseBranch =>
    let (cmdsTest, transTest, env', tc', lc') := translate_expr test env tc lc
    let (cmdsThen, env'', tc'', lc'') := translate_stm thenBranch env' tc' lc'
    let (cmdsElse, env''', tc''', lc''') := translate_stm elseBranch env'' tc'' lc''

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
    let (cmdsTest, transTest, env', tc', lc') := translate_expr test env tc lc
    let (cmdsBody, env'', tc'', lc'') := translate_stm body env' tc' lc'

    let (labelGuard, lc''') := Label.bumpAndCreate lc''
    let (labelDone, lc'''') := Label.bumpAndCreate lc'''

    ([.label labelGuard]
    ++ cmdsBody
    ++ cmdsTest
    ++ [.ite transTest labelGuard labelDone]
    , env''
    , tc''
    , lc'''')

  | .ret valOpt =>
    match valOpt with
    | some retVal =>
      let (cmdsRetVal, transRetVal, env', tc', lc') := translate_expr retVal env tc lc
      (cmdsRetVal ++ [.ret (some transRetVal)], env', tc', lc')
    | none => ([.ret none], env, tc, lc)


  | .seq first rest =>
    let (cmdsFirst, env', tc', lc') := translate_stm first env tc lc
    let (cmdsRest, env'', tc'', lc'') := translate_stm rest env' tc' lc'

    (cmdsFirst ++ cmdsRest
    , env''
    , tc''
    , lc'')

  -- TODO: weave in type info into TempEnv
  | .declare varName _ value =>
    let (temp, tc') := Temp.bumpAndCreate tc
    let (cmdsValue, env', tc'', lc') := translate_stm value env tc' lc
    (cmdsValue, env'.insert varName temp, tc'', lc')

  | .defn varName _ =>
    let (temp, tc') := Temp.bumpAndCreate tc
    ([], env.insert varName temp, tc', lc)

  | .asop _ _ _ => panic! "[Error] asops should have been elaborated away but found in translate_stm"
  | .forLit _ _ _ _ => panic! "[Error] for should have been elaborated away but found in translate_stm"

  | .expr mexpr =>
    let (cmds, _, env', tc', lc') := translate_expr mexpr env tc lc
    (cmds, env', tc', lc')

  | .nop => ([], env, tc, lc)

  -- TODO
  | .assert _ => panic! "[Error] unimplemented (assert)"
  | .error _ => panic! "[Error] unimplemented (error)"
  | .annotation _ => panic! "[Error] unimplemented (annotation)"

def translate_tau : Ast.Tau → Tree.Tau
  | .int | .char | .bool => .int
  | .string => panic! "[Error] strings are not yet handled"
  | .void => .void

def translate_param (param : Ast.Param) : Tree.Param :=
  let (tau, varName) := param
  (translate_tau tau, varName)

def translate_gdecl (gdecl : Ast.GDecl) : Tree.FunctionDef :=
  match gdecl with
  | .fdecl _ _ _ _ => panic! "[Error] fdecls should have been elaborated away but found in translate_gdecl"
  | .typedef _ _ => panic! "[Error] typedefs should have been elaborated away but found in translate_gdecl"
  | .fdefn retType fname params body _ =>
    let (cmds, _, _, _) := (List.foldl
      (λ (cmdsAcc, envAcc, tcAcc, lcAcc) mstm =>
        let (cmds, env', tc', lc') := translate_stm mstm envAcc tcAcc lcAcc
        (cmdsAcc ++ cmds, env', tc', lc')
      )
      ([], {}, 0, 0)
      body)
    (fname
    , translate_tau retType
    , List.map translate_param params
    , cmds)

def translate (program : Ast.Program) : Tree.Program :=
  List.map translate_gdecl program

end C0Boole.Tree.Trans
