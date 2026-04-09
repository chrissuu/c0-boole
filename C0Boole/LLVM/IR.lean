import C0Boole.Utils.Label
import C0Boole.Utils.Temp
open C0Boole.Utils.Label
open C0Boole.Utils.Temp

namespace C0Boole.LLVM.IR

inductive Tau where
  | i1
  | i8
  | i32
  | void
deriving Inhabited


abbrev Var := Temp
abbrev VarName := String
abbrev Arg := Tau × VarName

inductive BinOp where
  | add
  | sub
  | mul
  | sdiv
  | srem
  | and
  | xor
  | or
  | shl
  | ashr
  | slt
  | sgt
  | sle
  | sge
  | eq
  | ne

inductive Expr where
  | nop

  /-- Types are enforced upstream by typechecker. At this point, types are only needed for LLVM emitting,
  so treating (most) types as 32-bit bitvectors allows for the full range of Tau's to be represented
  conveniently. -/
  | bitVec (bitVec : BitVec 32)
  | var (t : Temp)
  | binop (op : BinOp) (tau : Tau) (lhs : Expr) (rhs : Expr)
  | call (tau : Tau) (fname : String) (args : List Expr)

inductive Stm where
  | assign (var : Var) (val : Expr)
  | callVoid (fname : String) (args : List Expr)
  | label (l : Label)
  | brJump (l : Label)
  | brIte (val : Expr) (thenBranch : Label) (elseBranch : Label)
  | ret (val : Expr)

abbrev FunctionDef := String × Tau × List Arg × List Stm
abbrev Program := List FunctionDef

end C0Boole.LLVM.IR
