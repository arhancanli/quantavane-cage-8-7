module

public import Cage87

public section

/-!
# Proof of the statement in `Challenge.lean`

The theorem below has exactly the statement of its counterpart in `Challenge.lean` (Comparator
checks this). The witness is the graph `G` of `Cage87.Bridge`, given by the adjacency lists of
`Cage87.Data`; `isRegular` and `girth_eq` are proved there from the kernel checks of
`Cage87.Chunks`.
-/

namespace Cage87

theorem exists_regular_girth_seven :
    ∃ (G : SimpleGraph (Fin 768)) (_ : DecidableRel G.Adj), G.IsRegularOfDegree 8 ∧ G.girth = 7 :=
  ⟨G, inferInstance, isRegular, girth_eq⟩

end Cage87
