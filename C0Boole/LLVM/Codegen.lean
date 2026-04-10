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

def isAtom : Tree.Expr → Bool
  | .const _ | .temp _ => true
  | _ => false

abbrev FEnv := Std.HashMap String (IR.Tau × List IR.Tau)

def translateExpr (expr : Tree.Expr) (tc : TempCounter) (fenv : FEnv) : List IR.Stm × IR.Expr × TempCounter :=
  match expr with
  | .const val =>
    ( []
    , .bitVec (BitVec.ofInt 32 (Int32.toInt val))
    , tc)

  | .temp t =>
    ( []
    , .var t
    , tc)

  | .binop op lhs rhs =>
    let tau : IR.Tau := if isCmpOp op then .i1 else .i32
    let (stmsLhs, transLhs, tc') := translateExpr lhs tc fenv
    let (stmsRhs, transRhs, tc'') := translateExpr rhs tc' fenv
    ( stmsLhs ++ stmsRhs
    , .binop (translateBinOp op) tau transLhs transRhs
    , tc''
    )

  | .call fname args =>
    let (stms, transArgs, tc') :=
      List.foldr
      (λ expr (stmsAcc, argsAcc, tcAcc) =>
        let (stms', expr', tc') := translateExpr expr tcAcc fenv
        (stms' ++ stmsAcc, expr' :: argsAcc, tc')
      )
      ([], [], tc)
      args
    let (retTau, argsTau) := fenv.get! fname
    match retTau with
    | .void =>
      ( stms ++ [.callVoid fname (List.zip argsTau transArgs)]
      , .nop
      , tc'
      )
    | _ =>
      ( stms
      , .call retTau fname (List.zip argsTau transArgs)
      , tc'
      )

def translateTau : Tree.Tau → IR.Tau
  | .int => .i32
  | .void => .void

def mkFenv (program : Tree.Program) : FEnv :=
  List.foldl
  (λ env (fname, tau, args, _) =>
    env.insert fname (translateTau tau,
    List.map (λ (tau, _) => translateTau tau) args))
  {}
  program


def translateCmd (cmd : Tree.Command) (tc : TempCounter) (lc : LabelCounter) (fenv : FEnv): List IR.Stm × TempCounter × LabelCounter :=
  match cmd with
  | .move dest src =>
    let (stms, expr, tc') := translateExpr src tc fenv

    ( stms ++ [ .assign dest expr ]
    , tc'
    , lc
    )

  | .ite test thenBranch elseBranch =>
    let (stms, transTest, tc') := translateExpr test tc fenv

    ( stms ++ [ .brIte transTest thenBranch elseBranch]
    , tc'
    , lc
    )

  | .goto l =>

    ( [.brJump l]
    , tc
    , lc
    )

  | .label l =>

    ( [.label l]
    , tc
    , lc
    )

  | .ret valOpt =>
    match valOpt with
    | some expr =>
      let (stms, transExpr, tc') := translateExpr expr tc fenv

      ( stms ++ [ .ret transExpr ]
      , tc'
      , lc
      )

    | none =>

      ( [.ret .nop ]
      , tc
      , lc
      )

def translateArg (arg : Tree.Arg) : IR.Arg :=
  let (tau, argName) := arg
  (translateTau tau, argName)

def translateArgs (args : List Tree.Arg) : List IR.Arg := List.map translateArg args

def translateFdefn (fdefn : Tree.FunctionDef) (tc : TempCounter) (lc : LabelCounter) (fenv : FEnv) : IR.FunctionDef × TempCounter × LabelCounter :=
  let (fname, tau, args, cmds) := fdefn
  let (transCmds, tc', lc') :=
    List.foldr
    (λ cmd (stmsAcc, tcAcc, lcAcc) =>
      let (stms, tc', lc') := translateCmd cmd tcAcc lcAcc fenv
      (stms ++ stmsAcc, tc', lc')
    )
    ([], tc, lc)
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
  let (transProgram, _, _) :=
    List.foldr
    (λ fdefn (fdefnAcc, tcAcc, lcAcc) =>
      let (transFdefn, tc', lc') := translateFdefn fdefn tcAcc lcAcc fenvInit
      (transFdefn :: fdefnAcc, tc', lc')
    )
    ([], tcInit, lcInit)
    program

  transProgram

end C0Boole.LLVM.Codegen
