module

public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
# An 8-regular graph of girth 7 on 768 vertices: the statement

This file is the statement of record. It imports only Mathlib and states the result with `sorry`.
`Solution.lean` proves it; `comparator.json` names the compared theorem. No definitions of our own
are used.

## Cages

The *girth* of a graph is the length of its shortest cycle (`SimpleGraph.girth` in Mathlib; it is
`0` for a graph without cycles). A `(k, g)`-*cage* is a `k`-regular graph of girth `g` with the
fewest vertices, and `n(k, g)` is its number of vertices. Exact values are known only for a few
small `k` and `g`; for most pairs, upper bounds come from constructions. The House of Graphs keeps a
table of the best known upper bounds (the cage table of G. Exoo, J. Goedgebeur, J. Jooken and
others).

## The result

* `exists_regular_girth_seven`: there is an 8-regular simple graph of girth 7 on 768 vertices.
  Hence `n(8, 7) ≤ 768`.

When this was written (12 November 2026), the House of Graphs cage table listed `n(8, 7) ≤ 774`
(Exoo, Goedgebeur, Jooken, Stubbe and Van den Eede, 2026). The Moore bound for girth 7 is
`1 + 8 + 8 · 7 + 8 · 7² = 457`, so `457 ≤ n(8, 7) ≤ 768`.
-/

namespace Cage87

/-- **An 8-regular graph of girth 7 on 768 vertices.** The `DecidableRel` instance only serves to
count neighbours (`SimpleGraph.degree`); the degree does not depend on it. -/
theorem exists_regular_girth_seven :
    ∃ (G : SimpleGraph (Fin 768)) (_ : DecidableRel G.Adj), G.IsRegularOfDegree 8 ∧ G.girth = 7 := by
  sorry

end Cage87
