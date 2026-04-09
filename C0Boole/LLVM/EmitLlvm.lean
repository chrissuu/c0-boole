import C0Boole.Ast
import C0Boole.LLVM.IR
open C0Boole
open C0Boole.Ast
open C0Boole.LLVM.IR

namespace C0Boole.LLVM.Codegen

def emitTau : IR.Tau → String
  | .i1 => "i1"
  | .i8 => "i8"
  | .i32 => "i32"
  | .void => "void"

def emitBinOp : IR.BinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .sdiv => "sdiv"
  | .srem => "srem"
  | .and => "and"
  | .xor => "xor"
  | .or => "or"
  | .shl => "shl"
  | .ashr => "ashr"
  | .slt => "slt"
  | .sgt => "sgt"
  | .sle => "sle"
  | .sge => "sge"
  | .eq => "eq"
  | .ne => "ne"

def emitArgs (args : List IR.Arg) : String :=
  ", ".intercalate (List.map (λ (tau, varName) => s!"{emitTau tau} %{varName}") args)

mutual
def emitFEvals (args : List IR.Expr) : String :=
  ", ".intercalate (List.map emitVal args)


def emitVal : IR.Expr → String
  | .bitVec bv => toString (Int32.ofInt (bv.toInt))
  | .var t => t.name
  | .binop op tau lhs rhs =>
    s!"{emitBinOp op} {emitTau tau} {emitVal lhs} {emitVal rhs}"
  | .call tau fname args =>
    s!"call {emitTau tau} @{fname}({emitFEvals args})"
  | .nop => ""

end

def emitStm (retTau : IR.Tau) : IR.Stm → String
  | .assign var val => s!"%{var.name} = {emitVal val}"

  | .callVoid fname args =>
    s!"call void @{fname}({emitFEvals args})"

  | .label l =>
    s!"{l.name}:"

  | .brJump l =>
    s!"br label %{l.name}"

  | .brIte val thenBranch elseBranch =>
    s!"br i1 {emitVal val}, label %{thenBranch.name}, label %{elseBranch.name}"

  | .ret val =>
    match retTau with
    | .void => s!"ret void"
    | _ => s!"ret {emitTau retTau} {emitVal val}"

def emitFdefn (fdefn : IR.FunctionDef) : String :=
  let (fname, tau, args, stms) := fdefn
  let emitStms := stms.map (emitStm tau)
  let markIndent := stms.map (fun stm => match stm with | .label _ => false | _ => true)

  let formattedEmitStm :=
    (List.zip markIndent emitStms)
      |> List.map (fun (indent, rawEmitStm) =>
        if indent then "\t" ++ rawEmitStm else rawEmitStm)
      |> String.intercalate "\n"

  "define {emitTau tau} "
  ++ s!"@{fname}({emitArgs args}) "
  ++ "{"
  ++ "\n"
  ++ formattedEmitStm
  ++ "\n"
  ++ "}"

def emit (program : IR.Program) (fileName : String): IO Unit :=
  let rawProgram := "\n\n".intercalate (List.map emitFdefn program)
  IO.FS.writeFile fileName rawProgram

end C0Boole.LLVM.Codegen
