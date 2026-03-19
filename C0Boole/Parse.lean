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
def satisfyKind (f : Lexer.TokenKind -> Option a) : P a :=
  tokenMap (fun tk => f tk.kind)

-- "Expect" primitive: consume and return the next token when `pred` matches.
def expectKindTok (pred : Lexer.TokenKind -> Bool) : P Tok :=
  tokenFilter (fun tk => pred tk.kind)

-- Same as `expectKindTok` but discard the token payload.
def expectKind (pred : Lexer.TokenKind -> Bool) : P Unit := do
  let _ ← expectKindTok pred
  pure ()

def only (tok : Lexer.TokenKind) := (fun t => t == tok)

def lParen : P Unit := expectKind (fun | .lParen => true | _ => false)
def rParen : P Unit := expectKind (fun | .rParen => true | _ => false)
def comma : P Unit := expectKind (fun | .comma => true | _ => false)
def semicolon : P Unit := expectKind (fun | .semicolon => true | _ => false)
def kwReturn : P Unit := expectKind (fun | .kwReturn => true | _ => false)
def eofTok : P Unit := expectKind (fun | .eof => true | _ => false)
def qmark : P Unit := expectKind (fun | .question => true | _ => false)
def colon : P Unit := expectKind (fun | .colon => true | _ => false)

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
def withConsumedSpan (p : P a) : P (a × Option SrcSpan) := do
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

mutual
def parseParenExpr : P MarkedExpr := do
  let lTok ← expectKindTok (fun | .lParen => true | _ => false)
  let e ← parseExpr
  let rTok ← expectKindTok (fun | .rParen => true | _ => false)
  pure { e with
    span := some (spanFromTokenBounds lTok rTok)
  }

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
    | .sub => some .negative
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

def parseBitAndOp : P BinOp :=
  satisfyKind (fun
    | .and => some .bitAnd
    | _ => none)

def parseBitXorOp : P BinOp :=
  satisfyKind (fun
    | .xor => some .xor
    | _ => none)

def parseBitOrOp : P BinOp :=
  satisfyKind (fun
    | .or => some .bitOr
    | _ => none)

def parseLandOp : P BinOp :=
  satisfyKind (fun
    | .land => some .land
    | _ => none)

def parseLorOp : P BinOp :=
  satisfyKind (fun
    | .lor => some .lor
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
  let opsRev ← Parser.foldl (fun acc op => op :: acc) [] parseUnOp
  let ops := opsRev.reverse
  let base ← parseAtom
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

def parseShiftExpr : P MarkedExpr :=
  parseLeftAssoc parseAddExpr parseShiftOp

def parseCompExpr : P MarkedExpr :=
  parseLeftAssoc parseShiftExpr parseCompOp

def parseEqExpr : P MarkedExpr :=
  parseLeftAssoc parseCompExpr parseEqOp

def parseBitAndExpr : P MarkedExpr :=
  parseLeftAssoc parseEqExpr parseBitAndOp

def parseBitXorExpr : P MarkedExpr :=
  parseLeftAssoc parseBitAndExpr parseBitXorOp

def parseBitOrExpr : P MarkedExpr :=
  parseLeftAssoc parseBitXorExpr parseBitOrOp

def parseLandExpr : P MarkedExpr :=
  parseLeftAssoc parseBitOrExpr parseLandOp

def parseLorExpr : P MarkedExpr :=
  parseLeftAssoc parseLandExpr parseLorOp

def parseCondExpr : P MarkedExpr := do
  let firstTest ← parseLorExpr
  -- Parse chained conditional segments and fold right:
  -- a ? b : c ? d : e  ==>  a ? b : (c ? d : e)
  let (pairsRev, finalElse) ← Parser.foldl
    (fun (acc : List (MarkedExpr × MarkedExpr) × MarkedExpr) seg =>
      let (pairs, currTest) := acc
      let (thenBranch, nextTest) := seg
      ((currTest, thenBranch) :: pairs, nextTest))
    ([], firstTest)
    (do
      qmark
      let thenBranch ← parseLorExpr
      colon
      let nextTest ← parseLorExpr
      pure (thenBranch, nextTest))
  let pairs := pairsRev.reverse
  pure <| List.foldr
    (fun (test, thenBranch) elseBranch => mkExpr (.ternary test thenBranch elseBranch))
    finalElse
    pairs

def parseExpr : P MarkedExpr :=
  parseCondExpr

end

def parseReturnStm : P MarkedStm := do
  let kwTok ← expectKindTok (only .kwReturn)
  let value? ← option? parseExpr
  let semiTok ← expectKindTok (only .semicolon)
  pure { node := .ret value?
       , span := some (spanFromTokenBounds kwTok semiTok)
       }

def parseAssignStm : P MarkedStm := do
  let idTok ← expectKindTok (fun | .ident _ => true | _ => false)
  let op ← parseAssignOp
  let rhs ← parseExpr
  let semiTok ← expectKindTok (only .semicolon)
  let varName :=
    match idTok.kind with
    | .ident name => name
    | _ => ""
  let span := some (spanFromTokenBounds idTok semiTok)
  match op with
  | .assign => pure { node := .assign varName rhs, span := span }
  | _ => pure { node := .asop varName op rhs, span := span }

def parseExprStm : P MarkedStm := do
  let (e, exprSpan) ← withConsumedSpan parseExpr
  let semiTok ← expectKindTok (only .semicolon)
  let stmSpan :=
    match exprSpan with
    | some sp => some { startLoc := sp.startLoc, endLoc := semiTok.span.endLoc, fileName := sp.fileName }
    | none => some semiTok.span
  pure { node := .expr e, span := stmSpan }

def parseStm : P MarkedStm :=
  parseReturnStm <|> parseAssignStm <|> parseExprStm

def parseTau : P Tau :=
  satisfyKind (fun
    | .kwInt => some .int
    | .kwBool => some .bool
    | .kwVoid => some .void
    | _ => none)

def parseTypedef : P GDecl := do
  let _ ← expectKindTok (only .kwTypedef)
  let tau ← parseTau
  let aliasIdent ← parseIdent
  let _ ← expectKindTok (only .semicolon)
  pure (.typedef tau aliasIdent)

def parseParam : P Param := do
  let tau ← parseTau
  let paramName ← parseIdent
  pure (tau, paramName)

def parseFdecl : P GDecl := do
  let tau ← parseTau
  let fname ← parseIdent
  let _ ← expectKindTok (only .lParen)
  let params ← Parser.foldl (fun acc param => param :: acc) [] parseParam
  let _ ← expectKindTok (only .rParen)
  let _ ← expectKindTok (only .semicolon)
  pure (.fdecl tau fname params)


def parseFdefn : P GDecl := do
  let tau ← parseTau
  let fname ← parseIdent
  let _ ← expectKindTok (only .lParen)
  let params ← Parser.foldl (fun acc param => param :: acc) [] parseParam
  let _ ← expectKindTok (only .rParen)
  let _ ← expectKindTok (only .lBrace)
  let stms ← Parser.foldl (fun acc stm => stm :: acc) [] parseStm
  let _ ← expectKindTok (only .rBrace)
  pure (.fdefn tau fname params stms)

def parseGdecl : P GDecl :=
  parseTypedef <|> parseFdefn <|> parseFdecl

def runParser {a : Type} (p : P a) (tokens : List Tok) : Except String a :=
  -- Accept optional lexer-emitted EOF token, then require end of token stream.
  match Parser.run (p <* optional eofTok <* endOfInput) (Parser.Stream.mkOfList tokens) with
  | .ok _ x => .ok x
  | .error _ _ => .error "parse error"

def parseExprFromTokens (tokens : List Tok) : Except String MarkedExpr :=
  runParser parseExpr tokens

def parseStmFromTokens (tokens : List Tok) : Except String MarkedStm :=
  runParser parseStm tokens

def parseGdeclFromTokens (tokens : List Tok) : Except String GDecl :=
  runParser parseGdecl tokens

def parseProgramFromTokens (tokens : List Tok) : Except String Program := do
  runParser (Parser.foldl (fun acc decl => decl :: acc) [] parseGdecl) tokens
