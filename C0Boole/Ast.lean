/-
AST Core Definitions

See C0 reference manual here: https://c0.cs.cmu.edu/docs/c0-reference.pdf

Author: Chris Su <chrjs@cmu.edu>
-/
import C0Boole.SrcSpan

namespace C0Boole

inductive AssignOp where
  | assign -- assignment
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
  | incr
  | decr

inductive Tau where
  | int
  | bool
  | void

mutual
inductive Expr where
  | var   (name : String)
  | intLit (val : Int32)
  | binop (op : BinOp) (lhs : MarkedExpr) (rhs : MarkedExpr)
  | unop (op : UnOp) (operand : MarkedExpr)
  | ternary (test : MarkedExpr) (thenBranch : MarkedExpr) (elseBranch : MarkedExpr)
  | trueLit
  | falseLit
  | call (fname : String) (args : List MarkedExpr)

structure MarkedExpr where
  node : Expr
  span : Option SrcSpan

end

mutual
inductive Stm where
  | assign (varName : String) (val : MarkedExpr)
  -- this encapsulates both ite and if statements. If no elseBranch is needed, the elseBranch is simply Nop
  | ifLit (test : MarkedExpr) (thenBranch : MarkedStm) (elseBranch : MarkedStm)
  | whileLit (test : MarkedExpr) (body : MarkedStm)
  -- none in the case of void functions.
  | ret (valOpt : Option MarkedExpr)
  | seq (first : MarkedStm) (rest : MarkedStm)
  -- the value is of type MarkedStm and not MarkedExpr, since it translates nicely to scoping rules
  | declare (varName : String) (type : Tau) (value : MarkedStm)
  | asop (varName : String) (op : AssignOp) (value : MarkedExpr)
  | forLit (init : MarkedStm) (test : MarkedExpr) (update : MarkedStm) (body : MarkedStm)
  -- handles well-typed lines of the form [MarkedExpr];
  | expr : MarkedExpr -> Stm
  | assert (test : MarkedExpr)
  | nop

structure MarkedStm where
  node : Stm
  span : Option SrcSpan

end

abbrev Param := Tau × String

inductive GDecl where
  | fdecl (retType : Tau) (fname : String) (params : List Param)
  | fdefn (retType : Tau) (fname : String) (params : List Param) (body : List MarkedStm)
  | typedef (type : Tau) (alias : String)

abbrev Program := List GDecl

namespace Print

def ppAssignOp : AssignOp → String
  | .assign => "="
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
  | .incr => "++"
  | .decr => "--"

def ppTau : Tau → String
  | .int => "int"
  | .bool => "bool"
  | .void => "void"

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
      s!"{ppUnOp op}({ppMarkedExpr operand})"
  | .binop op lhs rhs =>
      s!"({ppMarkedExpr lhs} {ppBinOp op} {ppMarkedExpr rhs})"
  | .ternary test thenBranch elseBranch =>
      s!"({ppMarkedExpr test} ? {ppMarkedExpr thenBranch} : {ppMarkedExpr elseBranch})"
  | .call fname args =>
      let argsStr := String.intercalate ", " (args.map ppMarkedExpr)
      s!"{fname}({argsStr})"

partial def ppMarkedExpr (e : MarkedExpr) : String :=
  ppExpr e.node

end

mutual

partial def ppStm : Stm → String
  | .assign id e =>
      s!"{id} = {ppMarkedExpr e};"
  | .ret valOpt =>
      match valOpt with
      | some e => s!"return {ppMarkedExpr e};"
      | none => "return;"
  | .nop =>
      "/* nop */"
  | .expr e =>
      s!"{ppMarkedExpr e};"
  | .assert test =>
      s!"assert({ppMarkedExpr test});"
  | .declare id tau body =>
      let bodyStr := ppStm body.node
      if bodyStr.isEmpty || bodyStr == "/* nop */" then
        s!"{ppTau tau} {id};"
      else
        s!"{ppTau tau} {id};\n{bodyStr}"
  | .seq s1 s2 =>
      s!"{ppMarkedStm s1}\n{ppMarkedStm s2}"
  | .ifLit cond thenBranch elseBranch =>
      let thenStr := indent (ppMarkedStm thenBranch)
      let elseStr := ppMarkedStm elseBranch
      if elseStr == "/* nop */" then
        s!"if ({ppMarkedExpr cond}) \{\n{thenStr}\n}"
      else
        s!"if ({ppMarkedExpr cond}) \{\n{thenStr}\n} else \{\n{indent elseStr}\n}"
  | .whileLit cond body =>
      s!"while ({ppMarkedExpr cond}) \{\n{indent (ppMarkedStm body)}\n}"
  | .forLit init cond update body =>
      s!"for ({trimTrailingSemicolon (ppMarkedStm init)}; {ppMarkedExpr cond}; {trimTrailingSemicolon (ppMarkedStm update)}) \{\n{indent (ppMarkedStm body)}\n}"
  | .asop id op e =>
      s!"{id} {ppAssignOp op} {ppMarkedExpr e};"

partial def ppMarkedStm (s : MarkedStm) : String :=
  ppStm s.node

end

def ppStms (stms : List MarkedStm) : String :=
  String.intercalate "" (stms.map fun stm => indent (ppMarkedStm stm) ++ "\n")

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
      s!"{spaces indentLevel}Assign({id}, {ppMarkedExpr e})"
  | .ret valOpt =>
      let retStr := match valOpt with | some e => ppMarkedExpr e | none => "None"
      s!"{spaces indentLevel}Return({retStr})"
  | .nop =>
      s!"{spaces indentLevel}Nop"
  | .expr e =>
      s!"{spaces indentLevel}Expr({ppMarkedExpr e})"
  | .declare id tau body =>
      s!"{spaces indentLevel}Declare({id}, {ppTau tau},\n{ppMarkedStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .seq s1 s2 =>
      s!"{spaces indentLevel}Seq(\n{ppMarkedStmRaw (indentLevel + 1) s1},\n{ppMarkedStmRaw (indentLevel + 1) s2}\n{spaces indentLevel})"
  | .ifLit cond thenBranch elseBranch =>
      s!"{spaces indentLevel}If({ppMarkedExpr cond},\n{ppMarkedStmRaw (indentLevel + 1) thenBranch},\n{ppMarkedStmRaw (indentLevel + 1) elseBranch}\n{spaces indentLevel})"
  | .whileLit cond body =>
      s!"{spaces indentLevel}While({ppMarkedExpr cond},\n{ppMarkedStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .forLit init cond update body =>
      s!"{spaces indentLevel}For(\n{ppMarkedStmRaw (indentLevel + 1) init},\n{spaces (indentLevel + 1)}{ppMarkedExpr cond},\n{ppMarkedStmRaw (indentLevel + 1) update},\n{ppMarkedStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .asop id op e =>
      s!"{spaces indentLevel}Asop({id}, {ppAssignOp op}, {ppMarkedExpr e})"
  | .assert test =>
      s!"{spaces indentLevel}Assert({ppMarkedExpr test})"

partial def ppMarkedStmRaw (indentLevel : Nat) (stm : MarkedStm) : String :=
  ppStmRaw indentLevel stm.node

end

def ppStmsRaw (stms : List MarkedStm) : String :=
  String.intercalate "\n" (stms.map (ppMarkedStmRaw 0))

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

instance : ToString Program where
  toString := Print.ppProgram

end C0Boole
