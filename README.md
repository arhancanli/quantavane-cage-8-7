# An 8-regular graph of girth 7 on 768 vertices

A Lean 4 proof, with Mathlib, that there is an 8-regular simple graph of girth 7 on 768 vertices.
Hence the order of an `(8, 7)`-cage is at most 768; the House of Graphs cage table listed 774 when
this was written. It is laid out for registration on [Palomar](https://palomar-registry.org):
`Challenge.lean` states the result, `Solution.lean` proves it, and `comparator.json` names the
compared theorem.

## The result

The *girth* of a graph is the length of its shortest cycle. A `(k, g)`-*cage* is a `k`-regular graph
of girth `g` with as few vertices as possible, and `n(k, g)` is its number of vertices. For most
pairs `(k, g)` only bounds are known: the Moore bound below, and constructions above.

**Theorem.** There is an 8-regular simple graph of girth 7 on 768 vertices. Hence
`n(8, 7) ≤ 768`. (The Moore bound gives `n(8, 7) ≥ 1 + 8 + 8 · 7 + 8 · 7² = 457`.)

## What is compared (`comparator.json`)

| Lean name | What it says |
|---|---|
| `Cage87.exists_regular_girth_seven` | There are `G : SimpleGraph (Fin 768)` and `DecidableRel G.Adj` with `G.IsRegularOfDegree 8` and `G.girth = 7`. |

`definition_names` is empty: the statement uses Mathlib's `SimpleGraph`, `IsRegularOfDegree` (every
vertex has degree 8) and `girth` (the infimum of the lengths of the cycles, as a natural number).
The `DecidableRel` instance only serves to count neighbours; degrees do not depend on it.

## How the proof goes

- **The data** (`Cage87/Data.lean`). The neighbours of each vertex `0, …, 767`, stored in a binary
  trie so that Lean's kernel finds a vertex's list in ten steps. `scripts/make_data.py` wrote the
  file from the graph's sparse6 file and checked the graph first (degrees, and girth 7 by
  breadth-first search from every vertex). The Lean proof does not rely on that check or on the
  script.
- **The checks** (`Cage87/Check.lean`, `Cage87/Chunks.lean`). Lean's kernel evaluates, by
  `decide +kernel`: `wf_ok`, that every list has 8 distinct entries below 768, none equal to its
  own vertex, and that adjacency is symmetric; and, in 8 chunks of 96 vertices, the *branch check*:
  for every vertex `v` and every two neighbours `x ≠ y` of `v`, the branch of `v` through `x` and
  the branch through `y` are disjoint. The branch through `x` is the set of ends of the
  non-backtracking walks of length 1, 2 and 3 that start with the edge `v x`: `x`, the neighbours
  `y ≠ v` of `x`, and the neighbours `z ≠ x` of those `y`. Sets of vertices are bitmasks, so
  disjointness is one `land` of natural numbers. The checks take about 45 seconds.
- **The graph** (`Cage87/Bridge.lean`). `G` is the graph on `Fin 768` in which `u` and `v` are
  adjacent when `v` is in the list of `u`; `wf_ok` makes it a simple graph of degree 8 at every
  vertex (`degree_eq`).
- **No short cycles** (`seven_le_length`). Let `v₀ v₁ … v_{ℓ-1} v₀` be a cycle with `3 ≤ ℓ ≤ 6`
  (Mathlib's `Walk.IsCycle`; its vertices are distinct). Then `v_{⌊ℓ/2⌋}` is the end of the walk
  `v₀ v₁ …` of length `⌊ℓ/2⌋` and of the walk `v₀ v_{ℓ-1} …` of length `⌈ℓ/2⌉`, both at most 3
  and non-backtracking because the cycle's vertices are distinct. So it lies in the branch of `v₀`
  through `v₁` and in the branch through `v_{ℓ-1}`, and `v₁ ≠ v_{ℓ-1}`: the branch check at `v₀`
  forbids this. Every cycle therefore has length at least 7.
- **A 7-cycle** (`cycle7`): `0, 14, 398, 67, 468, 83, 387`, with its adjacencies and the cycle
  property checked by `decide +kernel`. With the previous point, `G.girth = 7` (`girth_eq`).

No `sorry` outside `Challenge.lean`, no `native_decide`, no extra axioms:
`lake env lean scripts/CheckAxioms.lean` prints `[propext, Classical.choice, Quot.sound]`.

## Why it is of interest

Cages are a classical topic of extremal graph theory (Tutte 1947; Erdős and Sachs 1963), and small
regular graphs of given girth are sought by algebraic constructions and computer search. The House
of Graphs keeps the table of the best known upper bounds on `n(k, g)` (the cage table of G. Exoo,
J. Goedgebeur, J. Jooken and others). For `(k, g) = (8, 7)` it listed 774 (Exoo, Goedgebeur, Jooken,
Stubbe and Van den Eede, 2026) when this was written. The graph here has 768 vertices. The natural
readers are researchers in extremal graph theory and finite geometry working on cages and on
regular graphs of given girth.

## Provenance, literature and novelty

The graph is the case `q = 7` of a construction found by Quantavane in November 2026 and listed on
quantavane.com. It starts from the incidence graph of the generalized quadrangle `W(7)` (800
vertices, 8-regular, girth 8) and from G. Kiss's construction (Art Discrete Appl. Math. 8 (2025)
#P3.04, Theorem 8: `n(q + 1, 7) ≤ 2q³ + 2q²`, 784 for `q = 7`), which deletes the `2(q + 1)` points
of a hyperbolic pair of lines `l₁, l₂` and joins the `(q + 1)²` lines meeting both, row by row, into
cycles. In addition, the lines of two whole rows (16 lines) are deleted, and on each deleted line
the `q - 1` points left one neighbour short are paired up by a matching with a fixed difference
of exponents, different in the two rows; `800 - 16 - 16 = 768`. The general statement (a `(q + 1)`-regular graph of girth 7
on `(q + 1)(2q² - r(q))` vertices for every odd prime power `q ≥ 7`) and its proof are not part of
this formalization; only the graph for `q = 7` is, and its regularity and girth are checked here
directly from its adjacency lists, so they do not depend on that proof or on our programs.

Bounds for this cell in the literature: `2q³ + 2q² - q = 777` (Abreu, Araujo-Pardo, Balbuena,
Labbate and Salas, Electron. J. Combin. 22(3) (2015) P3.5, as corrected in 2016), Kiss's 784, and
774 (Exoo, Goedgebeur, Jooken, Stubbe and Van den Eede, *New small regular graphs of given girth:
the cage problem and beyond*, Electron. J. Combin. 33(3) (2026) P3.48, arXiv:2511.07247), the value the House of Graphs table listed on 12 November 2026. A search of the
literature and of the table on 12 November 2026 found no 8-regular graph of girth 7 with fewer than
774 vertices. The search was limited, so novelty is our reading of it, not an established fact.

Data: `Cage87/Data.lean` was generated by `scripts/make_data.py` from the sparse6 file of the graph
(SHA-256 of the uncompressed file
`95683e1cbf3169111cdb138e30264a8f92ce774e08c28004afa02c67830b3eae`).

## Authorship and the role of AI

Author and maintainer: Arhan Canli (Quantavane), who takes responsibility for the result.

The construction, the checks, every program and every line of Lean here were produced by AI agents
(Claude, by Anthropic) working for Quantavane under Arhan Canli's direction. No mathematician outside
Quantavane has reviewed the proof.

## Checking it

Lean `v4.35.0` (`lean-toolchain`) and Mathlib `v4.35.0`
(`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lake-manifest.json`).

```sh
lake exe cache get        # prebuilt Mathlib
lake build                # Cage87, Challenge, Solution (the kernel checks take about a minute)
lake env lean scripts/CheckAxioms.lean
lake comparator           # Linux with bubblewrap: compares Challenge and Solution and replays the proofs
python3 scripts/make_data.py GRAPH.s6 .   # regenerates Data.lean and Chunks.lean from the sparse6 file
```

`.github/workflows/palomar-preflight.yml` runs Palomar's own mechanical check
(`PalomarRegistry/PalomarSubmission`, pinned commit) on every push to `main`.

## Files

- `Challenge.lean`: the statement of record (Mathlib imports only).
- `Solution.lean`: the compared theorem with its proof.
- `Cage87/Check.lean`: the kernel-evaluated checks (Lean core only).
- `Cage87/Data.lean`: the adjacency lists (generated).
- `Cage87/Chunks.lean`: the kernel checks (generated).
- `Cage87/Bridge.lean`: the graph, its degrees, the girth.
- `comparator.json`, `formalization.yaml`, `scripts/CheckAxioms.lean`, `scripts/make_data.py`.

## Licence

Apache-2.0 (`LICENSE`).
