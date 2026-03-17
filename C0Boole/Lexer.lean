/-
Lexer & Tokens

See C0 reference manual here: https://c0.cs.cmu.edu/docs/c0-reference.pdf

Author: Chris Su <chrjs@cmu.edu>
-/
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


/-
All match* functions below assume that the first
character of the slice is the respective Token seed.
Hence, the slice that is returned includes the seed.
If it could not successfully match the pattern, it will
return none.
-/

end C0Boole.Lexer
