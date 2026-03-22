/-
Elaboration

Desugars the any syntactic sugar of C0 and makes some conveniences as to
allow for better proof automation by Boole and relevant backends.

Currently, the following are elaborated:
1. Assignment ops
2. Unary ops (!, ~, -)
3. For loops
4. Typedefs
5. &&, || operators

Depending on whether we want to allow a "do-faithful-translation" functionality,
we may want to have a flag that turns the elaborator on and off.

Since typechecker (mostly) works on the elaborated AST, we can still resume
typechecking on the elaborated AST, but lowering to Boole happens on the original
AST.

Author: Chris Su <chrjs@cmu.edu>
-/

import C0Boole.Ast
open C0Boole
open C0Boole.Ast

namespace C0Boole.Elab
partial def countUnopOfType (acc : Nat) (type : UnOp) (mexp : MarkedExpr) :=
  match mexp.node with
  | .unop type' mexp' => if type = type' then countUnopOfType (acc + 1) type mexp' else (acc, mexp)
  | _ => (acc, mexp)

def mkElabExpr (node : Expr) (span : Option SrcSpan) : MarkedExpr :=
  MarkedExpr.mk node span

def mkElabStm (node : Stm) (span : Option SrcSpan) : MarkedStm :=
  MarkedStm.mk node span

partial def elabMExpr (mexp : MarkedExpr) :=
  match mexp.node with
  | .binop op lhs rhs =>
    match op with
    | .land =>
      mkElabExpr
        (.ternary (elabMExpr lhs) (elabMExpr rhs) (mkElabExpr .falseLit mexp.span))
        mexp.span
    | .lor =>
      mkElabExpr
        (.ternary (elabMExpr lhs) (mkElabExpr .trueLit mexp.span) (elabMExpr rhs))
        mexp.span
    | _ => mkElabExpr (.binop op (elabMExpr lhs) (elabMExpr rhs)) mexp.span
  | .unop op mexp' =>
    match op with
    | .bang =>
      let (numBangs, reducedMexp) := countUnopOfType 0 .bang mexp'
      if numBangs % 2 = 0 then mkElabExpr (elabMExpr reducedMexp).node mexp.span
      else mkElabExpr (.unop .bang (elabMExpr reducedMexp)) mexp.span
    | .bitNot =>
      let (numBitNot, reducedMexp) := countUnopOfType 0 .bitNot mexp'
      if numBitNot % 2 = 0 then mkElabExpr (elabMExpr reducedMexp).node mexp.span
      else mkElabExpr (.unop .bitNot (elabMExpr reducedMexp)) mexp.span

      -- parity collapsing for this is probably not safe to do, so for now ignore parity collapsing
    | .negative => mkElabExpr (.binop .sub (mkElabExpr (.intLit 0) mexp.span) (elabMExpr mexp')) mexp.span
    | .decr => mkElabExpr (.binop .sub (elabMExpr mexp') (mkElabExpr (.intLit 1) mexp.span)) mexp.span
    | .incr => mkElabExpr (.binop .plus (elabMExpr mexp') (mkElabExpr (.intLit 1) mexp.span)) mexp.span
  | .ternary test thenBranch elseBranch =>
    mkElabExpr (.ternary (elabMExpr test) (elabMExpr thenBranch) (elabMExpr elseBranch)) mexp.span
  | .call fname args =>
    mkElabExpr (.call fname (List.map elabMExpr args)) mexp.span
  | _ => mexp

def assignOpToBinOp : AssignOp → Option BinOp
  | .assign => none
  | .plusEq => some .plus
  | .subEq => some .sub
  | .mulEq => some .mul
  | .divEq => some .div
  | .modEq => some .mod
  | .bitAndEq => some .bitAnd
  | .xorEq => some .xor
  | .bitOrEq => some .bitOr
  | .shlEq => some .shl
  | .shrEq => some .shr

partial def elabMStm (mstm : MarkedStm) :=
  match mstm.node with
  | .assign varName val => mkElabStm (.assign varName (elabMExpr val)) mstm.span
  | .ifLit test thenBranch elseBranch =>
    mkElabStm (.ifLit (elabMExpr test) (elabMStm thenBranch) (elabMStm elseBranch)) mstm.span
  | .whileLit test body => mkElabStm (.whileLit (elabMExpr test) (elabMStm body)) mstm.span
  | .ret valOpt =>
    match valOpt with
    | some val => mkElabStm (.ret (some (elabMExpr val))) mstm.span
    | none => mkElabStm (.ret none) mstm.span
  | .seq first rest =>
    let span := spanCoverOpt first.span rest.span
    mkElabStm (.seq (elabMStm first) (elabMStm rest)) span
  | .declare varName tau value => mkElabStm (.declare varName tau (elabMStm value)) mstm.span
  | .asop varName op value =>
    match assignOpToBinOp op with
    | none => mkElabStm (.assign varName (elabMExpr value)) mstm.span
    | some binop =>
      let lhs := mkElabExpr (.var varName) mstm.span
      let rhs := mkElabExpr (.binop binop lhs (elabMExpr value)) mstm.span
      mkElabStm (.assign varName rhs) mstm.span
  | .forLit init test update body =>
    let bodySpan := spanCoverOpt body.span update.span
    let whileSpan := spanCoverOpt test.span bodySpan
    let forSpan := spanCoverOpt init.span whileSpan
    let desugaredBody := mkElabStm (.seq body update) bodySpan
    let desugaredWhile := mkElabStm (.whileLit test desugaredBody) whileSpan
    let desugaredFor := mkElabStm (.seq init desugaredWhile) forSpan
    elabMStm desugaredFor
  | .expr e => mkElabStm (.expr (elabMExpr e)) mstm.span
  | .assert test => mkElabStm (.assert (elabMExpr test)) mstm.span
  | .error e => mkElabStm (.error (elabMExpr e)) mstm.span
  | _ => mstm

def elabGDecl (gdecl : GDecl) : GDecl :=
  match gdecl with
  | .fdefn retType fname params body =>
    .fdefn retType fname params (List.map elabMStm body)
  | _ => gdecl

def elabProgram (program : Ast.Program) : Except String Ast.Program :=
  .ok (List.map elabGDecl program)

end C0Boole.Elab
