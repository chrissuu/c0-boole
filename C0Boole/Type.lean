import C0Boole.Ast
import Std.Data.HashMap
import Std.Data.HashSet

open C0Boole.Ast
open Std.HashMap
open Std.HashSet

namespace C0Boole.Typechecker
structure FEnv where
  retType : Tau
  fname : String
  params : List Param

def collectFEnv (program : Ast.Program) : Std.HashMap String FEnv :=
  program.foldl
    (fun env gdecl =>
      match gdecl with
      | .fdecl retType fname params _ =>
          env.insert fname { retType := retType, fname := fname, params := params }
      | .fdefn retType fname params _ _ =>
          env.insert fname { retType := retType, fname := fname, params := params }
      | _ => env)
    {}

abbrev DEnv := Std.HashSet String

partial def tcUseDefMExpr (mexpr : Ast.MarkedExpr) (env : DEnv) : Except String Unit := do
  match mexpr.node with
  | .var name =>
    if env.contains name then
      .ok ()
    else .error s!"Used {name} before defined"
  | .binop _ lhs rhs =>
    let _ ← tcUseDefMExpr lhs env
    let _ ← tcUseDefMExpr rhs env
    .ok ()
  | .unop _ operand =>
    let _ ← tcUseDefMExpr operand env
    .ok ()

  |.ternary test thenVal elseVal =>
    let _ ← tcUseDefMExpr test env
    let _ ← tcUseDefMExpr thenVal env
    let _ ← tcUseDefMExpr elseVal env
    .ok ()

  | .call _ args =>
    args.forM (fun arg => tcUseDefMExpr arg env)

  -- TODO
  | .length arrayLike =>
    tcUseDefMExpr arrayLike env

  | .intLit _
  | .trueLit
  | .falseLit
  | .charLit _
  | .stringLit _
  | .result
  | .hastag
    => .ok ()

partial def tcUseDefMStm (mstm : Ast.MarkedStm) (env : DEnv) : Except String DEnv := do
  match mstm.node with
  | .assign varName val =>
    if not (env.contains varName) then
      .error s!"variable {varName} used before decl"

    let _ ← tcUseDefMExpr val env
    .ok env

  | .ifLit test thenBranch elseBranch =>
    let _ ← tcUseDefMExpr test env
    let env' ← tcUseDefMStm thenBranch env
    let env'' ← tcUseDefMStm elseBranch env'
    .ok env''

  | .whileLit test body =>
    let _ ← tcUseDefMExpr test env
    tcUseDefMStm body env

  | .declare varName _ value =>
    if env.contains varName then
      .error s!"variable {varName} declared more than once"

    let env' ← tcUseDefMStm value env
    .ok (env'.insert varName)

  | .defn varName _ =>
    if env.contains varName then
      .error s!"variable {varName} declared more than once"

    .ok (env.insert varName)

  | .ret valOpt =>
    match valOpt with
    | some val =>
      let _ ← tcUseDefMExpr val env
      .ok env
    | none => .ok env

  | .seq first rest =>
    let env' ← tcUseDefMStm first env
    tcUseDefMStm rest env'

  | .asop varName _ value =>
    if env.contains varName then
      let _ ← tcUseDefMExpr value env
      .ok env
    else
      .error s!"Used {varName} before defined"

  | .forLit init test update body =>
    let env' ← tcUseDefMStm init env
    let _ ← tcUseDefMExpr test env'
    let env'' ← tcUseDefMStm body env'
    tcUseDefMStm update env''

  | .expr e =>
    let _ ← tcUseDefMExpr e env
    .ok env

  | .assert test =>
    let _ ← tcUseDefMExpr test env
    .ok env

  | .error e =>
    let _ ← tcUseDefMExpr e env
    .ok env

  | .nop =>
    .ok env

  -- TODO
  | .annotation a =>
    match a.node with
    | .requires e
    | .ensures e
    | .asserts e
    | .loopInvariant e =>
      let _ ← tcUseDefMExpr e env
      .ok env

  | .incr varName
  | .decr varName =>
    if env.contains varName then
      .ok env
    else
      .error s!"Used {varName} before defined"

def tcUseDefGDecl (gdecl : Ast.GDecl) : Except String Unit := do
  match gdecl with
  | .fdefn (body := body) .. =>
    let _ ← List.foldlM (λ env mstm => tcUseDefMStm mstm env) {} body
    .ok ()
  | .fdecl .. => .ok ()
  | .typedef .. => .ok ()

def tcControlFlow (gdecl : Ast.GDecl) : Except String Unit :=
  match gdecl with
  | .fdefn (body := body) .. =>
    let containsReturn :=
      List.any
      (List.map (λ mstm => match mstm.node with | .ret _ => true | _ => false) body)
      id

    if containsReturn then
      .ok ()

    else .error "Could not find a return statement in function definition"

  | _ => .ok ()

def tc (program : Ast.Program) : Except String Unit := do
  List.forM program (λ gdecl => do
    let _ ← tcUseDefGDecl gdecl
    let _ ← tcControlFlow gdecl
    .ok ())

end C0Boole.Typechecker
