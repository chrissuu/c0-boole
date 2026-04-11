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

abbrev ValName := String
abbrev Arg := Tau × ValName

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
deriving Inhabited

inductive Val where
  | void
  | var (t : Temp)
  | ptr (t : Temp)
  /-- Types are enforced upstream by typechecker. At this point, types are only needed for LLVM emitting,
  so treating (most) types as 32-bit bitvectors allows for the full range of Tau's to be represented
  conveniently. -/
  | bitVec (bitVec : BitVec 32)
deriving Inhabited

inductive Expr where
  | binop (op : BinOp) (tau : Tau) (lhs : Val) (rhs : Val)
  | call (tau : Tau) (fname : String) (args : List (Tau × Val))
deriving Inhabited

inductive Stm where
  | assign (dest : Val) (exp : Expr)
  | callVoid (fname : String) (args : List (Tau × Val))
  | label (l : Label)
  | brJump (l : Label)
  | brIte (val : Val) (thenBranch : Label) (elseBranch : Label)
  | ret (val : Val)
  | alloca (ptr : Val) (type : Tau)
  | store (tau : Tau) (val : Val) (ptr : Val)
  | load (dest : Val) (tau : Tau) (ptr : Val)
deriving Inhabited

abbrev FunctionDef := String × Tau × List Arg × List Stm
abbrev Program := List FunctionDef

namespace Print
def ppTau : Tau → String
  | .i1 => "i1"
  | .i8 => "i8"
  | .i32 => "i32"
  | .void => "void"

end Print

end C0Boole.LLVM.IR
