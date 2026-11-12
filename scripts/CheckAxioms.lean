module

import Solution

/-!
# Axiom check

`lake env lean scripts/CheckAxioms.lean` (after `lake build`) prints the axioms that the compared
theorem of `Solution.lean` depends on. Palomar permits only `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms Cage87.exists_regular_girth_seven
