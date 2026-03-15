namespace C0Boole

/-- Location in a source file. -/
structure SrcLoc where
  line : Nat
  col  : Nat
deriving Repr, BEq, DecidableEq

/-- Span in a source file. -/
structure SrcSpan where
  startLoc : SrcLoc
  endLoc   : SrcLoc
  file     : String
deriving Repr, BEq, DecidableEq

def SrcSpan.show (s : SrcSpan) : String :=
  s!"{s.file}:{s.startLoc.line}:{s.startLoc.col}-{s.endLoc.line}:{s.endLoc.col}"

end C0Boole
