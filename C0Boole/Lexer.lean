/-
Lexer & Tokens

See C0 reference manual here: https://c0.cs.cmu.edu/docs/c0-reference.pdf

We currently opt for a simple maximal munch lexer. It is mostly efficient enough to
handle modest programs, while also being simple enough to debug and iterate
quickly on. If Lean develops a lexer library, considering migrating this code
to the lexer library.

Author: Chris Su <chrjs@cmu.edu>
-/
import Std
import C0Boole.SrcSpan

namespace C0Boole.Lexer
inductive TokenKind where
  | ident (name : String)
  | intLit (value : Int)
  | hexLit (value : String)
  | stringLit (value : String)
  | charLit (value : Char)

  -- Core Keywords
  -- C0 reference, page 16, section 14
  -- The reserved keywords of the language are:
  -- int bool string char void struct typedef
  -- if else while for continue break return assert
  -- error true false NULL alloc alloc_array
  | kwInt | kwBool | kwString | kwChar | kwVoid | kwStruct | kwTypedef
  | kwIf | kwElse | kwWhile | kwFor | kwReturn | kwAssert
  | kwError | kwTrue | kwFalse | kwNull | kwAlloc | kwAllocArray
  | kwContinue | kwBreak -- Note: nice to haves
  | kwUse -- #use (for libraries (& headers?))

  -- Contracts / Annotations Keywords
  -- C0 reference, page 18, section 14.3
  | requires
  | ensures
  | loopInvariant
  | result
  | length
  | hastag

  -- Syntax
  | lParen | rParen     -- ()
  | lBrace | rBrace     -- {}
  | lBracket | rBracket -- []
  | colon | semicolon   -- :;
  | comma | question    -- ,?

  -- Assignment Operators
  | equal
  | plusEq
  | subEq
  | mulEq
  | divEq
  | modEq
  | andEq
  | xorEq
  | orEq
  | shlEq
  | shrEq

  -- Operators
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
  | land -- &&
  | lor  -- ||
  | and  -- &
  | xor
  | or   -- |
  | shl
  | shr

  | incr -- ++
  | decr -- --

  | bang     -- !
  | squiggly -- ~
  | negative -- -

  | int
  | bool
  | void
  | typedef

  | openMultilineComment -- /*
  | closeMultilineComment -- */
  | comment -- //

  | eof

structure Token where
  kind : TokenKind
  span : SrcSpan

def tokenKindOptionOfString : String → Option TokenKind
  -- Static lexemes only. Dynamic lexemes (identifiers, literals) return `none`.
  | "int" => some .kwInt
  | "bool" => some .kwBool
  | "string" => some .kwString
  | "char" => some .kwChar
  | "void" => some .kwVoid
  | "struct" => some .kwStruct
  | "typedef" => some .kwTypedef
  | "if" => some .kwIf
  | "else" => some .kwElse
  | "while" => some .kwWhile
  | "for" => some .kwFor
  | "return" => some .kwReturn
  | "assert" => some .kwAssert
  | "error" => some .kwError
  | "true" => some .kwTrue
  | "false" => some .kwFalse
  | "NULL" => some .kwNull
  | "alloc" => some .kwAlloc
  | "alloc_array" => some .kwAllocArray
  | "continue" => some .kwContinue
  | "break" => some .kwBreak
  | "#use" => some .kwUse
  | "\\requires" => some .requires
  | "\\ensures" => some .ensures
  | "\\loop_invariant" => some .loopInvariant
  | "\\result" => some .result
  | "\\length" => some .length
  | "#" => some .hastag
  | "(" => some .lParen
  | ")" => some .rParen
  | "{" => some .lBrace
  | "}" => some .rBrace
  | "[" => some .lBracket
  | "]" => some .rBracket
  | ":" => some .colon
  | ";" => some .semicolon
  | "," => some .comma
  | "?" => some .question
  | "=" => some .equal
  | "+=" => some .plusEq
  | "-=" => some .subEq
  | "*=" => some .mulEq
  | "/=" => some .divEq
  | "%=" => some .modEq
  | "&=" => some .andEq
  | "^=" => some .xorEq
  | "|=" => some .orEq
  | "<<=" => some .shlEq
  | ">>=" => some .shrEq
  | "+" => some .plus
  | "-" => some .sub
  | "*" => some .mul
  | "/" => some .div
  | "%" => some .mod
  | "<" => some .lt
  | "<=" => some .lte
  | ">" => some .gt
  | ">=" => some .gte
  | "==" => some .eq
  | "!=" => some .neq
  | "&&" => some .land
  | "||" => some .lor
  | "&" => some .and
  | "^" => some .xor
  | "|" => some .or
  | "<<" => some .shl
  | ">>" => some .shr
  | "++" => some .incr
  | "--" => some .decr
  | "!" => some .bang
  | "~" => some .squiggly
  | "/*" => some .openMultilineComment
  | "*/" => some .closeMultilineComment
  | "//" => some .comment
  | _ => none

def marker (fileName : String) (lineNumber : Nat) (leftCol : Nat) (rightCol : Nat) : SrcSpan :=
  SrcSpan.mk (SrcLoc.mk lineNumber leftCol) (SrcLoc.mk lineNumber rightCol) (fileName)

/--
Maximal Munch Lexer

A seed for some token T is any character c which prefixes T.
A character c may be a seed for more than one token T. For each
token T that c is a seed for, we try to munch that pattern maximally.
This returns the length of the matched string as well as the Token that we
retrieved. We take the argmax amongst this set w.r.t retrieved string length.
We then jump our character pointer to after the string length, ignoring whitespaces.
The SrcLoc ptr is updated in these instances: Tabs, Return, etc.

ident       ::= ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*
integer     ::= ("0" | ['1'-'9'](['0'-'9']*))
hexadecimal ::= "0"['x' 'X']['0'-'9' 'a'-'f' 'A'-'F']+
ws          ::= [' ' '\t' '\r' '\011' '\012']
-/


def isHexLitSeed c := c == '0'

def isIntLitSeed c := Char.isDigit c

def isIdentSeed c := Char.isAlpha c || c == '_'

def isStringLitSeed c := c == '\"'

def isCharLitSeed c := c == '\''

def isCommentSeed c := c == '/'

def isSeed c :=
  isHexLitSeed c
  || isIntLitSeed c
  || isIdentSeed c
  || isStringLitSeed c
  || isCharLitSeed c
  || isCommentSeed c

def isHexDigit (c : Char) : Bool :=
  Char.isDigit c
  || ('a' <= c && c <= 'f')
  || ('A' <= c && c <= 'F')

-- hexadecimal ::= "0"['x' 'X']['0'-'9' 'a'-'f' 'A'-'F']+
def matchHexLit (s : String.Slice) (sliceLength : Nat) : Option String.Slice :=
  if sliceLength < 3 then
    none
  else if !(s.startsWith "0x" || s.startsWith "0X") then
    none
  else
    let digits := (s.drop 2).takeWhile isHexDigit
    if digits.isEmpty then
      none
    else
      let consumed := 2 + digits.toString.length
      some (s.take consumed)

-- integer ::= ("0" | ['1'-'9'](['0'-'9']*))
def matchIntLit (s : String.Slice) (sliceLength : Nat) : Option String.Slice :=
  if sliceLength == 1 then
    if s.isNat then some s else none
  else if s.startsWith "0" then none
  else
    let digits := s.takeWhile Char.isDigit
    if digits.isEmpty then none
    else some digits

def isIdentChar (c : Char) : Bool :=
  c == '_' || c.isAlphanum

-- ident ::= ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*
def matchIdent (s : String.Slice) (_ : Nat) : Option String.Slice :=
  if s.startsWith Char.isDigit then none
  else
    let identChars := s.takeWhile isIdentChar
    if identChars.isEmpty then none
    else some identChars

def endsWithUnescapedQuote (s : String.Slice) : Bool :=
  if !s.endsWith "\"" then
    false
  else
    let beforeLast := s.dropEnd 1
    let trailingBackslashes := beforeLast.takeEndWhile (λ c => c == '\\')
    trailingBackslashes.toString.length % 2 == 0

def matchStringLit (s : String.Slice) (sliceLength : Nat) : Option String.Slice :=
  if sliceLength < 2 then none
  else if !(s.startsWith "\"" && endsWithUnescapedQuote s) then none
  else some s

def isValidCharEscape (c : Char) : Bool :=
  c == 'n' || c == 't' || c == 'r' || c == '\\' || c == '\'' || c == '"' || c == '0'

def matchCharLit (s : String.Slice) (sliceLength : Nat) : Option String.Slice :=
  if sliceLength < 3 then none
  else if !s.startsWith "'" then none
  else
    let body := s.drop 1
    if body.startsWith "\\" then
      if sliceLength < 4 then none
      else
        let esc := (body.drop 1).take 1
        let close := (body.drop 2).take 1
        if esc.isEmpty || close.isEmpty then
          none
        else if close.toString != "'" then none
        else
          match esc.front? with
          | some c => if isValidCharEscape c
                      then some (s.take 4)
                      else none
          | none   => none
    else
      let ch := body.take 1
      let close := body.drop 1 |>.take 1
      if ch.isEmpty || close.isEmpty then none
      else if close.toString != "'" then none
      else some (s.take 3)

/-- Matches for the two types of supported comments: // until first \n or \r; /* ... */, which can span multiline -/
def matchComment (s : String.Slice) (_ : Nat) : Option String.Slice :=
  if s.startsWith "//" then
    let body := s.drop 2
    let commentBody := body.takeWhile (fun c => c != '\n' && c != '\r')
    let consumed := 2 + commentBody.toString.length
    some (s.take consumed)
  else if s.startsWith "/*" then
    match (s.drop 2).find? "*/" with
    | none => none
    | some endPos =>
      let body := s.drop 2
      let bodyStr := body.extract body.startPos endPos
      let consumed := 2 + bodyStr.length + 2
      some (s.take consumed)
  else
    none

def staticTokenLexemes : List String :=
  [
    "<<=", ">>=",
    "+=", "-=", "*=", "/=", "%=", "&=", "^=", "|=",
    "<=", ">=", "==", "!=", "&&", "||", "<<", ">>", "++", "--",
    "(", ")", "{", "}", "[", "]", ":", ";", ",", "?",
    "=", "+", "-", "*", "/", "%", "<", ">", "&", "^", "|", "!", "~", "#"
  ]

def matchStaticToken (s : String.Slice) (_ : Nat) : Option String.Slice :=
  (staticTokenLexemes.find? (fun lex => s.startsWith lex)).map (fun lex => s.take lex.length)

def getMatchesAndMaximalMatch (s : String.Slice) : List String.Slice × Option String.Slice :=
  let len := s.positions.length
  let patternMatches := [matchHexLit, matchIntLit, matchIdent, matchStringLit, matchCharLit, matchComment, matchStaticToken]
  |> List.map (λ fn => fn s len)
  |> List.filterMap id
  let maximalMatch := List.maxOn? (λ x => x.positions.length) patternMatches
  (patternMatches, maximalMatch)

structure WhiteSpaceInfo where
  numTabs : Nat     -- \t
  numCarRet : Nat   -- \r
  numNewlines : Nat -- \n
  numCrlf : Nat     -- \r\n

def countWhiteSpaceType (s : String.Slice) : WhiteSpaceInfo :=
  let numTabs := (s.split "\t").length - 1
  let numCarRet := (s.split "\r").length - 1
  let numNewlines := (s.split "\n").length - 1
  let numCrlf := (s.split "\r\n").length - 1

  { numTabs := numTabs
  , numCarRet := numCarRet - numCrlf -- subtract to avoid double counting
  , numNewlines := numNewlines - numCrlf
  , numCrlf := numCrlf
  }

def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\u000B' || c == '\u000C'

def decodeEscapedChar (c : Char) : Char :=
  match c with
  | 'n' => '\n'
  | 't' => '\t'
  | 'r' => '\r'
  | '\\' => '\\'
  | '\'' => '\''
  | '"' => '"'
  | '0' => '\u0000'
  | x => x

def advanceLocByChars : Nat → Nat → List Char → SrcLoc
  | line, col, [] => SrcLoc.mk line col
  | line, _, '\r' :: '\n' :: rest => advanceLocByChars (line + 1) 1 rest
  | line, _, '\r' :: rest => advanceLocByChars (line + 1) 1 rest
  | line, _, '\n' :: rest => advanceLocByChars (line + 1) 1 rest
  | line, col, '\t' :: rest => advanceLocByChars line (col + tabWidth) rest
  | line, col, _ :: rest => advanceLocByChars line (col + 1) rest

def advanceLocBySlice (line col : Nat) (s : String.Slice) : SrcLoc :=
  advanceLocByChars line col s.toString.toList

def toTokenKind? (matched : String.Slice) : Option TokenKind :=
  let lex := matched.toString
  if lex.startsWith "0x" || lex.startsWith "0X" then
    some (.hexLit lex)
  else if matched.startsWith "\"" then
    if lex.length < 2 then none
    else some (.stringLit ((matched.drop 1).dropEnd 1).toString)
  else if matched.startsWith "'" then
    if lex.length == 3 then
      match (matched.drop 1).front? with
      | some ch => some (.charLit ch)
      | none => none
    else if lex.length == 4 then
      match ((matched.drop 2).take 1).front? with
      | some esc => some (.charLit (decodeEscapedChar esc))
      | none => none
    else
      none
  else if matched.startsWith Char.isDigit then
    match lex.toNat? with
    | some n => some (.intLit (Int.ofNat n))
    | none => none
  else if matched.startsWith isIdentSeed then
    match tokenKindOptionOfString lex with
    | some kw => some kw
    | none => some (.ident lex)
  else
    tokenKindOptionOfString lex

partial def munch (fileName : String) (body : String) : List Token :=
  let rec go (s : String.Slice) (line col : Nat) (acc : List Token) : List Token :=
    if s.isEmpty then
      let loc := SrcLoc.mk line col
      let eof : Token := { kind := .eof, span := SrcSpan.mk loc loc fileName }
      (acc.reverse) ++ [eof]
    else
      let ws := s.takeWhile isWhitespace
      if !ws.isEmpty then
        let nextLoc := advanceLocBySlice line col ws
        go (s.drop ws.toString.length) nextLoc.line nextLoc.col acc
      else
        let (_, maximalMatch?) := getMatchesAndMaximalMatch s
        match maximalMatch? with
        | none =>
          -- Ensure progress even on unknown characters.
          let one := s.take 1
          let nextLoc := advanceLocBySlice line col one
          go (s.drop 1) nextLoc.line nextLoc.col acc
        | some matched =>
          let consumed := matched.toString.length
          let nextLoc := advanceLocBySlice line col matched
          if (matchComment s s.positions.length).isSome then
            go (s.drop consumed) nextLoc.line nextLoc.col acc
          else
            match toTokenKind? matched with
            | some kind =>
              let tok : Token := {
                kind := kind
                span := SrcSpan.mk (SrcLoc.mk line col) (SrcLoc.mk nextLoc.line nextLoc.col) fileName
              }
              go (s.drop consumed) nextLoc.line nextLoc.col (tok :: acc)
            | none =>
              go (s.drop consumed) nextLoc.line nextLoc.col acc
  go body.toSlice 1 1 []

end C0Boole.Lexer
