/-
AST Core Definitions

See C0 reference manual here: https://c0.cs.cmu.edu/docs/c0-reference.pdf

Author: Chris Su <chrjs@cmu.edu>
-/
import C0Boole.SrcSpan

namespace C0Boole

inductive AssignOp where
  | equal      -- assignment
  | plusEq     -- +=
  | subEq      -- -=
  | mulEq      -- *=
  | divEq      -- /=
  | modEq      -- %=
  | bitAndEq   -- &=
  | xorEq      -- ^=
  | bitOrEq    -- |=
  | shlEq      -- <<=
  | shrEq      -- >>=

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
  | land
  | lor
  | bitAnd
  | xor
  | bitOr
  | shl
  | shr

inductive UnOp where
  | bang
  | bitNot
  | negative

inductive Tau where
  | int
  | bool
  | void
  | typedef (alias : String)

mutual
inductive Expr where
  | var   (name : String)
  | intLit (val : Int32)
  | binop (op : BinOp) (lhs : MExpr) (rhs : MExpr)
  | unop (op : UnOp) (operand : MExpr)
  | ternary (test : MExpr) (thenBranch : MExpr) (elseBranch : MExpr)
  | trueLit
  | falseLit
  | call (fname : String) (args : List MExpr)

structure MExpr where
  node : Expr
  span : Option SrcSpan

end

mutual
inductive Stm where
  | assign (varName : String) (val : MExpr)
  -- this encapsulates both ite and if statements. If no elseBranch is needed, the elseBranch is simply Nop
  | ifLit (test : MExpr) (thenBranch : MStm) (elseBranch : MStm)
  | whileLit (test : MExpr) (body : MStm)
  -- none in the case of void functions.
  | ret (valOpt : Option MExpr)
  | seq (first : MStm) (rest : MStm)
  -- the value is of type MStm and not MExpr, since it translates nicely to scoping rules
  | declare (varName : String) (type : Tau) (value : MStm)
  | asop (varName : String) (op : AssignOp) (value : MExpr)
  | forLit (init : MStm) (test : MExpr) (update : MStm) (body : MStm)
  -- handles well-typed lines of the form [MExpr];
  | expr : MExpr -> Stm
  | assert (test : MExpr)
  | nop

structure MStm where
  node : Stm
  span : Option SrcSpan

end

abbrev Param := Tau × String

inductive GDecl where
  | fdecl (retType : Tau) (fname : String) (params : List Param)
  | fdefn (retType : Tau) (fname : String) (params : List Param) (body : List MStm)
  | typedef (type : Tau) (alias : String)

abbrev Program := List GDecl

namespace Print

def ppAssignOp : AssignOp → String
  | .equal => "="
  | .plusEq => "+="
  | .subEq => "-="
  | .mulEq => "*="
  | .divEq => "/="
  | .modEq => "%="
  | .bitAndEq => "&="
  | .xorEq => "^="
  | .bitOrEq => "|="
  | .shlEq => "<<="
  | .shrEq => ">>="

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
  | .land => "&&"
  | .lor => "||"
  | .bitAnd => "&"
  | .xor => "^"
  | .bitOr => "|"
  | .shl => "<<"
  | .shr => ">>"

def ppUnOp : UnOp → String
  | .bang => "!"
  | .bitNot => "~"
  | .negative => "-"

def ppTau : Tau → String
  | .int => "int"
  | .bool => "bool"
  | .void => "void"
  | .typedef alias => alias

private def indent (str : String) : String :=
  str.splitOn "\n"
    |> List.map (fun line => "  " ++ line)
    |> String.intercalate "\n"

private def trimTrailingSemicolon (str : String) : String :=
  match str.toList.reverse with
  | ';' :: rest => String.ofList rest.reverse
  | _ => str

private def spaces (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

mutual

partial def ppExpr : Expr → String
  | .var id => id
  | .intLit n => toString n
  | .trueLit => "true"
  | .falseLit => "false"
  | .unop op operand =>
      s!"{ppUnOp op}({ppMExpr operand})"
  | .binop op lhs rhs =>
      s!"({ppMExpr lhs} {ppBinOp op} {ppMExpr rhs})"
  | .ternary test thenBranch elseBranch =>
      s!"({ppMExpr test} ? {ppMExpr thenBranch} : {ppMExpr elseBranch})"
  | .call fname args =>
      let argsStr := String.intercalate ", " (args.map ppMExpr)
      s!"{fname}({argsStr})"

partial def ppMExpr (e : MExpr) : String :=
  ppExpr e.node

end

mutual

partial def ppStm : Stm → String
  | .assign id e =>
      s!"{id} = {ppMExpr e};"
  | .ret valOpt =>
      match valOpt with
      | some e => s!"return {ppMExpr e};"
      | none => "return;"
  | .nop =>
      "/* nop */"
  | .expr e =>
      s!"{ppMExpr e};"
  | .assert test =>
      s!"assert({ppMExpr test});"
  | .declare id tau body =>
      let bodyStr := ppStm body.node
      if bodyStr.isEmpty || bodyStr == "/* nop */" then
        s!"{ppTau tau} {id};"
      else
        s!"{ppTau tau} {id};\n{bodyStr}"
  | .seq s1 s2 =>
      s!"{ppMStm s1}\n{ppMStm s2}"
  | .ifLit cond thenBranch elseBranch =>
      let thenStr := indent (ppMStm thenBranch)
      let elseStr := ppMStm elseBranch
      if elseStr == "/* nop */" then
        s!"if ({ppMExpr cond}) \{\n{thenStr}\n}"
      else
        s!"if ({ppMExpr cond}) \{\n{thenStr}\n} else \{\n{indent elseStr}\n}"
  | .whileLit cond body =>
      s!"while ({ppMExpr cond}) \{\n{indent (ppMStm body)}\n}"
  | .forLit init cond update body =>
      s!"for ({trimTrailingSemicolon (ppMStm init)}; {ppMExpr cond}; {trimTrailingSemicolon (ppMStm update)}) \{\n{indent (ppMStm body)}\n}"
  | .asop id op e =>
      s!"{id} {ppAssignOp op} {ppMExpr e};"

partial def ppMStm (s : MStm) : String :=
  ppStm s.node

end

def ppStms (stms : List MStm) : String :=
  String.intercalate "" (stms.map fun stm => indent (ppMStm stm) ++ "\n")

def ppParam : Param → String
  | (tau, id) => s!"{ppTau tau} {id}"

def ppParams (params : List Param) : String :=
  let paramsStr := String.intercalate ", " (params.map ppParam)
  s!"({paramsStr})"

def ppGDecl : GDecl → String
  | .typedef tau id =>
      s!"typedef {ppTau tau} {id};"
  | .fdecl ret id params =>
      s!"{ppTau ret} {id}{ppParams params};"
  | .fdefn ret id params stms =>
      if stms.isEmpty then
        s!"{ppTau ret} {id}{ppParams params} \{\n}"
      else
        s!"{ppTau ret} {id}{ppParams params} \{\n{ppStms stms}}"

def ppProgram (program : Program) : String :=
  String.intercalate "\n\n" (program.map ppGDecl)

mutual

partial def ppStmRaw (indentLevel : Nat) : Stm → String
  | .assign id e =>
      s!"{spaces indentLevel}Assign({id}, {ppMExpr e})"
  | .ret valOpt =>
      let retStr := match valOpt with | some e => ppMExpr e | none => "None"
      s!"{spaces indentLevel}Return({retStr})"
  | .nop =>
      s!"{spaces indentLevel}Nop"
  | .expr e =>
      s!"{spaces indentLevel}Expr({ppMExpr e})"
  | .declare id tau body =>
      s!"{spaces indentLevel}Declare({id}, {ppTau tau},\n{ppMStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .seq s1 s2 =>
      s!"{spaces indentLevel}Seq(\n{ppMStmRaw (indentLevel + 1) s1},\n{ppMStmRaw (indentLevel + 1) s2}\n{spaces indentLevel})"
  | .ifLit cond thenBranch elseBranch =>
      s!"{spaces indentLevel}If({ppMExpr cond},\n{ppMStmRaw (indentLevel + 1) thenBranch},\n{ppMStmRaw (indentLevel + 1) elseBranch}\n{spaces indentLevel})"
  | .whileLit cond body =>
      s!"{spaces indentLevel}While({ppMExpr cond},\n{ppMStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .forLit init cond update body =>
      s!"{spaces indentLevel}For(\n{ppMStmRaw (indentLevel + 1) init},\n{spaces (indentLevel + 1)}{ppMExpr cond},\n{ppMStmRaw (indentLevel + 1) update},\n{ppMStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .asop id op e =>
      s!"{spaces indentLevel}Asop({id}, {ppAssignOp op}, {ppMExpr e})"
  | .assert test =>
      s!"{spaces indentLevel}Assert({ppMExpr test})"

partial def ppMStmRaw (indentLevel : Nat) (stm : MStm) : String :=
  ppStmRaw indentLevel stm.node

end

def ppStmsRaw (stms : List MStm) : String :=
  String.intercalate "\n" (stms.map (ppMStmRaw 0))

def ppGDeclRaw : GDecl → String
  | .typedef tau id =>
      s!"Typedef({ppTau tau}, {id})"
  | .fdecl ret id params =>
      s!"Fdecl({ppTau ret}, {id}, [{String.intercalate ", " (params.map ppParam)}])"
  | .fdefn ret id params stms =>
      s!"Fdefn({ppTau ret}, {id}, [{String.intercalate ", " (params.map ppParam)}], [\n{ppStmsRaw stms}\n])"

def ppProgramRaw (program : Program) : String :=
  s!"Program:\n{String.intercalate "\n" (program.map ppGDeclRaw)}"

end Print

end C0Boole
