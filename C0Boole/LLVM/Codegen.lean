import C0Boole.LLVM.Tree
import C0Boole.LLVM.IR
import C0Boole.Utils.Temp
import C0Boole.Utils.Label
import Std.Data.HashMap

open C0Boole.LLVM.Tree
open C0Boole.LLVM.IR
open C0Boole.Utils.Temp
open C0Boole.Utils.Label
open Std.HashMap

namespace C0Boole.LLVM.Codegen

def translateBinOp : Tree.BinOp → IR.BinOp
  | .plus => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .sdiv
  | .mod => .srem
  | .bitAnd => .and
  | .xor => .xor
  | .bitOr => .or
  | .shl => .shl
  | .shr => .ashr
  | .lt => .slt
  | .lte => .sgt
  | .gt => .sle
  | .gte => .sge
  | .eq => .eq
  | .neq => .ne

def isCmpOp : Tree.BinOp → Bool
  | .plus
  | .sub
  | .mul
  | .div
  | .mod
  | .bitAnd
  | .xor
  | .bitOr
  | .shl
  | .shr => false
  | .lt
  | .lte
  | .gt
  | .gte
  | .eq
  | .neq => true

def tauOfBinOp : Tree.BinOp → IR.Tau
  | .plus
  | .sub
  | .mul
  | .div
  | .mod
  | .bitAnd
  | .xor
  | .bitOr
  | .shl
  | .shr => .i32
  | .lt
  | .lte
  | .gt
  | .gte
  | .eq
  | .neq => .i1

def isAtom : Tree.Expr → Bool
  | .const _ | .temp _ => true
  | _ => false

structure FunctionInfo where
  retTau : IR.Tau
  argsTau : List IR.Tau
deriving Inhabited

abbrev FEnv := Std.HashMap String FunctionInfo

structure TempInfo where
  temp : Temp
  tau : IR.Tau
deriving Inhabited

abbrev TEnv := Std.HashMap String TempInfo

def ppTempInfo (tInfo : TempInfo) : String :=
  s!"{tInfo.temp.name} : {IR.Print.ppTau tInfo.tau}"

def translateExpr (expr : Tree.Expr) (tc : TempCounter) (fenv : FEnv) (tenv : TEnv): List IR.Stm × IR.Val × TempCounter × TEnv :=
  match expr with
  | .const val =>
    ( []
    , .bitVec (BitVec.ofInt 32 (Int32.toInt val))
    , tc
    , tenv)

  | .temp var =>
    -- Lookup var in env.
    -- If it exists, use it.
    -- Not existing in the env is an impossible case, since this implies it is used before
    -- being defined.
    match tenv.get? var.name with
    | some tempInfo =>
      ( []
      , .var tempInfo.temp
      , tc
      , tenv)
    | none =>
    -- dbg_trace (", ".intercalate (Std.HashMap.keys tenv))

    panic! s!"[Error] saw a var ({var.name}) used before being defined"

  | .binop op lhs rhs =>
    let tau : IR.Tau := if isCmpOp op then .i1 else .i32
    let (stmsLhs, transLhs, tc', tenv') := translateExpr lhs tc fenv tenv
    let (stmsRhs, transRhs, tc'', tenv'') := translateExpr rhs tc' fenv tenv'
    let (temp, tc''') := Temp.bumpAndCreate tc''
    ( stmsLhs ++ stmsRhs ++ [ .assign (.var temp) (.binop (translateBinOp op) tau transLhs transRhs) ]
    , .var temp
    , tc'''
    , tenv''
    )

  | .call fname args =>
    let (stms, transArgs, tc', tenv') :=
      List.foldr
      (λ expr (stmsAcc, argsAcc, tcAcc, tenvAcc) =>
        let (stms', expr', tc', tenv') := translateExpr expr tcAcc fenv tenvAcc
        (stms' ++ stmsAcc, expr' :: argsAcc, tc', tenv')
      )
      ([], [], tc, tenv)
      args
    let fInfo := fenv.get! fname
    let (retTau, argsTau) := (fInfo.retTau, fInfo.argsTau)
    match retTau with
    | .void =>
      ( stms ++ [.callVoid fname (List.zip argsTau transArgs)]
      , .void
      , tc'
      , tenv'
      )
    | _ =>
      let (temp, tc') := Temp.bumpAndCreate tc
      ( stms ++ [ .assign (.var temp) (.call retTau fname (List.zip argsTau transArgs)) ]
      , .var temp
      , tc'
      , tenv'
      )

def translateTau : Tree.Tau → IR.Tau
  | .int => .i32
  | .bool => .i1
  | .void => .void

def mkFenv (program : Tree.Program) : FEnv :=
  List.foldl
  (λ env (fname, tau, args, _) =>
    env.insert fname (FunctionInfo.mk (translateTau tau)
    (List.map (λ (tau, _) => translateTau tau) args))
  )
  {}
  program

def translateCmd (cmd : Tree.Command) (tc : TempCounter) (lc : LabelCounter) (fenv : FEnv) (tenv : TEnv) : List IR.Stm × TempCounter × LabelCounter × TEnv :=
  match cmd with
  | .move dest src =>
    match src with
    | .const val =>
      let (p, tc') := Temp.bumpAndCreate tc
      let (t, tc'') := Temp.bumpAndCreate tc'
      ( [ .alloca (.ptr p) .i32
        , .store .i32 (.bitVec (Int32.toBitVec val)) (.ptr p)
        , .load (.var t) .i32 (.ptr p)
        ]
      , tc''
      , lc
      , tenv.insert dest.name (TempInfo.mk t .i32)
      )

    | .temp t =>
      let tempInfo := tenv.get! t.name
      let (temp, tc') := Temp.bumpAndCreate tc
      let tempInfo' := TempInfo.mk temp tempInfo.tau
      match tempInfo.tau with
      | .i8 | .i32 =>
        ( [ .assign (.var temp) (.binop .add tempInfo.tau (.var t) (.bitVec (Int32.toBitVec 0))) ]
        , tc'
        , lc
        , tenv.insert dest.name tempInfo'
        )
      | .i1 =>
        ( [ .assign (.var temp) (.binop .or tempInfo.tau (.var t) (.bitVec (Int32.toBitVec 0)))]
        , tc'
        , lc
        , tenv.insert dest.name tempInfo'
        )

        | .void => panic! "[Error] vars should not have a void type"

    | .binop op lhs rhs =>
      let (stmsLhs, valLhs, tc', tenv') := translateExpr lhs tc fenv tenv
      let (stmsRhs, valRhs, tc'', tenv'') := translateExpr rhs tc' fenv tenv'
      let (temp, tc''') := Temp.bumpAndCreate tc''
      let binop : IR.Expr := .binop (translateBinOp op) (tauOfBinOp op) valLhs valRhs
      let tempInfo := TempInfo.mk temp (tauOfBinOp op)
      ( stmsLhs ++ stmsRhs ++ [ .assign (.var temp) binop]
      , tc'''
      , lc
      , tenv''.insert dest.name tempInfo
      )

    | .call fname args =>
      let fInfo := fenv.get! fname
      let (retTau, argsTau) := (fInfo.retTau, fInfo.argsTau)
      let (stms, transArgs, tc', tenv') := List.foldr
        (λ (tau, arg) (stmsAcc, valsAcc, tcAcc, tenvAcc) =>
          let (stmsArg, valArg, tc', tenv') := translateExpr arg tcAcc fenv tenvAcc
          (stmsArg ++ stmsAcc, (tau, valArg)::valsAcc, tc', tenv')
        )
        ([], [], tc, tenv)
        (List.zip argsTau args)
      let call : IR.Expr := .call retTau fname transArgs
      let (temp, tc'') := Temp.bumpAndCreate tc'
      ( stms ++ [ .assign (.var temp) call]
      , tc''
      , lc
      , tenv'.insert dest.name (TempInfo.mk temp retTau)
      )

  | .ite test thenBranch elseBranch =>
    let (stms, transTest, tc', tenv') := translateExpr test tc fenv tenv

    ( stms ++ [ .brIte transTest thenBranch elseBranch]
    , tc'
    , lc
    , tenv'
    )

  | .goto l =>

    ( [.brJump l]
    , tc
    , lc
    , tenv
    )

  | .label l =>

    ( [.label l]
    , tc
    , lc
    , tenv
    )

  | .ret valOpt =>
    match valOpt with
    | some expr =>
      let (stms, transExpr, tc', tenv') := translateExpr expr tc fenv tenv

      ( stms ++ [ .ret transExpr ]
      , tc'
      , lc
      , tenv'
      )

    | none =>

      ( [.ret .void ]
      , tc
      , lc
      , tenv
      )

def translateArg (arg : Tree.Arg) : IR.Arg :=
  let (tau, temp) := arg
  (translateTau tau, temp.name)

def translateArgs (args : List Tree.Arg) : List IR.Arg := List.map translateArg args

def translateFdefn (fdefn : Tree.FunctionDef) (tc : TempCounter) (lc : LabelCounter) (fenv : FEnv) : IR.FunctionDef × TempCounter × LabelCounter :=
  let (fname, tau, args, cmds) := fdefn
  let seededTEnv : TEnv := List.foldr
    (λ (tau, temp) (tenvAcc) => (tenvAcc.insert temp.name (TempInfo.mk temp (translateTau tau))))
    {}
    args

  let (transCmds, tc', lc', _) :=
    List.foldl
    (λ (stmsAcc, tcAcc, lcAcc, tenvAcc) cmd =>
      let (stms, tc', lc', tenv') := translateCmd cmd tcAcc lcAcc fenv tenvAcc
      (stmsAcc ++ stms, tc', lc', tenv')
    )
    ([], tc, lc, seededTEnv)
    cmds

  (
    ( fname
    , translateTau tau
    , translateArgs args
    , transCmds)
  , tc'
  , lc'
  )

def translate (program : Tree.Program) : IR.Program :=
  let fenvInit := mkFenv program
  let tcInit := 0
  let lcInit := 0

  -- dbg_trace s!"{Tree.Print.ppProgramRaw program}"
  let (transProgram, _, _) :=
    List.foldl
    (λ (fdefnAcc, tcAcc, lcAcc) fdefn =>
      let (transFdefn, tc', lc') := translateFdefn fdefn tcAcc lcAcc fenvInit
      (fdefnAcc ++ [transFdefn], tc', lc')
    )
    ([], tcInit, lcInit)
    program

  transProgram

end C0Boole.LLVM.Codegen
