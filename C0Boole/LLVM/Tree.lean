/-
Tree Representation

See C0 reference manual here: https://c0.cs.cmu.edu/docs/c0-reference.pdf

Author: Chris Su <chrjs@cmu.edu>
-/
import C0Boole.Utils.Temp
import C0Boole.Utils.Label

namespace C0Boole.LLVM.Tree

open C0Boole.Utils.Temp
open C0Boole.Utils.Label

-- TODO: maybe consider deduplicating this definition against AST.BinOp?
inductive BinOp where
  | plus
  | sub
  | mul
  | div
  | mod
  | lt
  | lte
  | gt
  | gte
  | eq
  | neq
  | bitAnd
  | xor
  | bitOr
  | shl
  | shr
deriving Inhabited

inductive Expr where
  | const (val : Int32)
  | temp (t : Temp)
  | binop (op : BinOp) (lhs : Expr) (rhs : Expr)
  | call (fname : String) (args : List Expr)
deriving Inhabited

inductive Command where
  | move (dest : Temp) (src : Expr)
  | ite (test : Expr) (thenBranch : Label) (elseBranch : Label)
  | goto (label : Label)
  | label (l : Label)
  | ret (valOpt : Option Expr)
deriving Inhabited

inductive Tau where
  | int
  | void
deriving Inhabited

abbrev VarName := String
abbrev Arg := Tau × VarName
abbrev FunctionDef := String × Tau × List Arg × List Command
abbrev Program := List FunctionDef

namespace Print

def ppBinOp : BinOp → String
  | .plus => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "%"
  | .lt => "<"
  | .lte => "<="
  | .gt => ">"
  | .gte => ">="
  | .eq => "=="
  | .neq => "!="
  | .bitAnd => "&"
  | .xor => "^"
  | .bitOr => "|"
  | .shl => "<<"
  | .shr => ">>"

def ppTau : Tau → String
  | .int => "int"
  | .void => "void"

def ppArg (arg : Arg) : String :=
  let (tau, varName) := arg
  s!"{ppTau tau} {varName}"

partial def ppExpr : Expr → String
  | .const val => toString val
  | .temp t => t.name
  | .binop op lhs rhs => s!"({ppExpr lhs} {ppBinOp op} {ppExpr rhs})"
  | .call fname args => s!"call {fname}({String.intercalate ", " (List.map ppExpr args)})"

def ppCommand : Command → String
  | .move dest src => s!"{dest.name} <- {ppExpr src};"
  | .ite test thenBranch elseBranch =>
      s!"if ({ppExpr test}) goto {thenBranch.name}; else goto {elseBranch.name};"
  | .goto label => s!"goto {label.name};"
  | .label l => s!"{l.name}:"
  | .ret valOpt =>
      match valOpt with
      | some val => s!"return {ppExpr val};"
      | none => "return;"

def ppFunctionDef (fdef : FunctionDef) : String :=
  let (fname, tau, args, commands) := fdef
  s!"{ppTau tau} {fname}({String.intercalate ", " (List.map ppArg args)}){String.intercalate "\n" (List.map ppCommand commands)}"

def ppProgram (program : Program) : String :=
  String.intercalate "\n" (program.map ppFunctionDef)

end Print

instance : ToString BinOp where
  toString := Print.ppBinOp

instance : ToString Expr where
  toString := Print.ppExpr

instance : ToString Command where
  toString := Print.ppCommand

instance : ToString Program where
  toString := Print.ppProgram

end C0Boole.LLVM.Tree
