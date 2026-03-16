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
  | boolLit (value : Bool)

  -- Keywords
  -- c0 reference, page 16, section 14
  -- The reserved keywords of the language are:
  -- int bool string char void struct typedef
  -- if else while for continue break return assert
  -- error true false NULL alloc alloc_array
  | kwInt | kwBool | kwString | kwChar | kwVoid | kwStruct | kwTypedef
  | kwIf | kwElse | kwWhile | kwFor | kwReturn | kwAssert
  | kwError | kwTrue | kwFalse | kwNull | kwAlloc | kwAllocArray
  | kwContinue | kwBreak -- Note: nice to haves
  | kwUse

  -- Contracts / Annotations
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
  | colon | semicolon
  | comma | question

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


def translate : TokenKind → String
  | .kwInt -> "int"
  |

end C0Boole.Lexer
