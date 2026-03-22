/-
Elaboration

Desugars the any syntactic sugar of C0 and makes some conveniences as to
allow for better proof automation by Boole and relevant backends.

Currently, the following are elaborated:
1. Assignment ops
2. Unary ops (!, ~, -)
3. For loops
4. Typedefs
5. Ternary operator
6. &&, || operators

Depending on whether we want to allow a "do-faithful-translation" functionality,
we may want to have a flag that turns the elaborator on and off.

Since typechecker (mostly) works on the elaborated AST, we can still resume
typechecking on the elaborated AST, but lowering to Boole happens on the original
AST.

Author: Chris Su <chrjs@cmu.edu>
-/
import C0Boole.Ast
open C0Boole.Ast

partial def countBang (acc : Nat) (mexp : MarkedExpr) :=
  match mexp.node with
  | .unop .bang mexp' => countBang (acc + 1) mexp'
  | _ => acc


def elabMarkedExpr mexp :=
  match mexp with
  | .assign => mexp
