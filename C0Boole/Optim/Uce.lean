/-
Unreachable Code Elimination

This eliminates unreachable code from the original program.
This should be done conservatively, however, compared to normal
UCE. For instance, a user may want to prove the properties of some
function, but not have to call the function anywhere. A normal UCE pass
may eliminate this function definition, however, our pass of UCE will
eliminate this function definition only if it has no contracts and
annotations.

Author: Chris Su <chrjs@cmu.edu>
-/
