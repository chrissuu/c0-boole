import Parser
import C0Boole.Ast
import C0Boole.Lexer

namespace C0Boole.Parse
open Parser
open C0Boole

abbrev Tok := C0Boole.Lexer.Token
abbrev TokStream := Parser.Stream.OfList Tok
abbrev P := SimpleParser TokStream Tok

def mkExpr (node : Expr) : MarkedExpr :=
  { node := node, span := none }

-- Consume one token and decode its `TokenKind` with `f`.
def satisfyKind (f : Lexer.TokenKind → Option α) : P α :=
  tokenMap (fun tk => f tk.kind)

-- "Expect" primitive: consume and return the next token when `pred` matches.
def expectKindTok (pred : Lexer.TokenKind → Bool) : P Tok :=
  tokenFilter (fun tk => pred tk.kind)

-- Same as `expectKindTok` but discard the token payload.
def expectKind (pred : Lexer.TokenKind → Bool) : P Unit := do
  let _ ← expectKindTok pred
  pure ()

def lParen : P Unit := expectKind (fun | .lParen => true | _ => false)
def rParen : P Unit := expectKind (fun | .rParen => true | _ => false)
def comma : P Unit := expectKind (fun | .comma => true | _ => false)
def semicolon : P Unit := expectKind (fun | .semicolon => true | _ => false)
def kwReturn : P Unit := expectKind (fun | .kwReturn => true | _ => false)
def eofTok : P Unit := expectKind (fun | .eof => true | _ => false)

def spanFromTokenBounds (startTok endTok : Tok) : SrcSpan :=
  { startLoc := startTok.span.startLoc
  , endLoc := endTok.span.endLoc
  , fileName := startTok.span.fileName
  }

def spanFromConsumed (consumed : List Tok) : Option SrcSpan :=
  match consumed with
  | [] => none
  | first :: rest =>
    let last := rest.foldl (fun _ tk => tk) first
    some (spanFromTokenBounds first last)

/-- Parse `p` and recover the span from consumed tokens. -/
def withConsumedSpan (p : P α) : P (α × Option SrcSpan) := do
  -- Snapshot stream before and after parsing `p`, then diff `past`.
  let before ← Parser.getStream
  let x ← p
  let after ← Parser.getStream
  let consumedRev := after.past.drop before.past.length
  pure (x, spanFromConsumed consumedRev.reverse)

def parseIdent : P String :=
  satisfyKind (fun
    | .ident name => some name
    | _ => none)

def parseIntLit : P MarkedExpr :=
  satisfyKind (fun
    | .intLit n => some (mkExpr (.intLit (Int32.ofInt n)))
    | _ => none)

def parseBoolLit : P MarkedExpr :=
  satisfyKind (fun
    | .kwTrue => some (mkExpr .trueLit)
    | .kwFalse => some (mkExpr .falseLit)
    | _ => none)

def parseVar : P MarkedExpr := do
  let (name, sp) ← withConsumedSpan parseIdent
  pure { node := .var name, span := sp }

def parseAtom : P MarkedExpr :=
  first [
    parseIntLit,
    parseBoolLit,
    parseVar,
    throwUnexpectedWithMessage none "expected expression atom"
  ]

def parseUnOp : P UnOp :=
  satisfyKind (fun
    | .bang => some .bang
    | .squiggly => some .bitNot
    | .negative => some .negative
    | .incr => some .incr
    | .decr => some .decr
    | _ => none)

def parseMulOp : P BinOp :=
  satisfyKind (fun
    | .mul => some .mul
    | .div => some .div
    | .mod => some .mod
    | _ => none)

def parseAddOp : P BinOp :=
  satisfyKind (fun
    | .plus => some .plus
    | .sub  => some .sub
    | _ => none)

def parseShiftOp : P BinOp :=
  satisfyKind (fun
    | .shl => some .shl
    | .shr => some .shr
    | _ => none)

def parseCompOp : P BinOp :=
  satisfyKind (fun
    | .lt  => some .lt
    | .lte => some .lte
    | .gt  => some .gt
    | .gte => some .gte
    | _ => none)

def parseEqOp : P BinOp :=
  satisfyKind (fun
    | .eq  => some .eq
    | .neq => some .neq
    | _ => none)

def parseAssignOp : P AssignOp :=
  satisfyKind (fun
    | .assign => some .assign
    | .plusEq => some .plusEq
    | .subEq  => some .subEq
    | .mulEq  => some .mulEq
    | .divEq  => some .divEq
    | .modEq  => some .modEq
    | .andEq  => some .bitAndEq
    | .xorEq  => some .xorEq
    | .orEq   => some .bitOrEq
    | .shlEq  => some .shlEq
    | .shrEq  => some .shrEq
    | _ => none)

def parseUnary : P MarkedExpr := do
  -- collect prefix unary operators
  let opsRev ← Parser.foldl (fun acc op => op :: acc) [] parseUnOp
  let ops := opsRev.reverse

  -- base expression
  let base ← parseAtom

  -- apply operators right-associatively: - ! x ==> -( !x )
  pure <| List.foldr (fun op acc => mkExpr (.unop op acc)) base ops

def parseLeftAssoc (term : P MarkedExpr) (op : P BinOp) : P MarkedExpr := do
  let lhs ← term
  let restRev ← Parser.foldl (fun acc x => x :: acc) [] do
    let o ← op
    let rhs ← term
    pure (o, rhs)
  let rest := restRev.reverse
  pure <| List.foldl (fun acc (o, rhs) => mkExpr (.binop o acc rhs)) lhs rest


def parseMulExpr : P MarkedExpr :=
  parseLeftAssoc parseUnary parseMulOp


def parseAddExpr : P MarkedExpr :=
  parseLeftAssoc parseMulExpr parseAddOp





def parseExpr : P MarkedExpr := do
  let lhs ← parseMulExpr
  -- Parse a left-associative chain: mulExpr (('+'|'-') mulExpr)*
  let restRev ← Parser.foldl (fun acc x => x :: acc) [] do
    let op ← parseAddOp
    let rhs ← parseMulExpr
    pure (op, rhs)
  let rest := restRev.reverse
  pure <| List.foldl (fun acc (op, rhs) => mkExpr (.binop op acc rhs)) lhs rest

def parseReturnStm : P MarkedStm := do
  let kwTok ← expectKindTok (fun | .kwReturn => true | _ => false)
  let value? ← option? parseExpr
  let semiTok ← expectKindTok (fun | .semicolon => true | _ => false)
  pure { node := .ret value?
       , span := some (spanFromTokenBounds kwTok semiTok)
       }

def parseExprStm : P MarkedStm := do
  let (e, exprSpan) ← withConsumedSpan parseExpr
  let semiTok ← expectKindTok (fun | .semicolon => true | _ => false)
  let stmSpan :=
    match exprSpan with
    | some sp => some { startLoc := sp.startLoc, endLoc := semiTok.span.endLoc, fileName := sp.fileName }
    | none => some semiTok.span
  pure { node := .expr e, span := stmSpan }

def parseStm : P MarkedStm :=
  parseReturnStm <|> parseExprStm

def runParser {α : Type} (p : P α) (tokens : List Tok) : Except String α :=
  -- Accept optional lexer-emitted EOF token, then require end of token stream.
  match Parser.run (p <* optional eofTok <* endOfInput) (Parser.Stream.mkOfList tokens) with
  | .ok _ x => .ok x
  | .error _ _ => .error "parse error"

def parseExprFromTokens (tokens : List Tok) : Except String MarkedExpr :=
  runParser parseExpr tokens

def parseStmFromTokens (tokens : List Tok) : Except String MarkedStm :=
  runParser parseStm tokens
