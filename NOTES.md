# Notes: what is proved and how it was checked (13 November 2026)

## What is proved

Proved in Lean 4 (v4.35.0, Mathlib v4.35.0) with no `sorry`, no `native_decide` and only the axioms
`propext`, `Classical.choice` and `Quot.sound`. The statement of record is in `Challenge.lean`;
`comparator.json` names the one compared theorem.

- `Cage87.exists_regular_girth_seven`: there are `G : SimpleGraph (Fin 768)` and a
  `DecidableRel G.Adj` with `G.IsRegularOfDegree 8` and `G.girth = 7` (Mathlib's girth). Hence
  `n(8, 7) ≤ 768`.

The kernel checks (`decide +kernel`): `wf_ok` (every adjacency list has 8 distinct entries below 768,
none equal to its vertex; adjacency is symmetric), `chunk_0` … `chunk_7` (the branch check of all
768 vertices, 96 per chunk), and the seven adjacencies and the cycle property of `cycle7`
(`0, 14, 398, 67, 468, 83, 387`). `scripts/make_data.py` checked the sparse6 file's SHA-256
(`95683e1cbf3169111cdb138e30264a8f92ce774e08c28004afa02c67830b3eae`, uncompressed), the degrees, the
girth (7, by breadth-first search from every vertex) and the branch condition before writing the
data; the Lean proof does not rely on any of these.

## Line counts

| File | Lines |
|---|---|
| `Challenge.lean` | 42 (1,677 bytes) |
| `Solution.lean` | 22 |
| `Cage87.lean` | 6 |
| `Cage87/Check.lean` | 90 |
| `Cage87/Data.lean` | 1,047 (generated) |
| `Cage87/Chunks.lean` | 49 (generated) |
| `Cage87/Bridge.lean` | 228 |
| `scripts/CheckAxioms.lean` | 13 |

Every `.lean` file starts with `module`; `Challenge.lean` imports only Mathlib
(`Mathlib.Combinatorics.SimpleGraph.Girth`, `Mathlib.Combinatorics.SimpleGraph.Finite`).

Mathlib's prebuilt cache for v4.35.0 lacked `Mathlib.Combinatorics.SimpleGraph.Girth` when this was
built (`lake exe cache get` reported the file missing upstream); Lake compiles that one module from
source in a few seconds.

## Checks run (Mac, Apple silicon, Lean v4.35.0, machine load about 50 to 60)

All on a fresh clone of commit `2410b6af9fff5893bd3103c099459b17c1de32f5` (the commit before this
file was added; no Lean file changed since), with the Lake packages of the pinned Mathlib checkout
and the project's own modules built from scratch. (An earlier run on a commit that differed only in a
docstring of `Cage87/Bridge.lean` gave the same results.)

1. `lake build`: every module built; `Cage87.Chunks` (the kernel checks) 44 s, peak 1.4 GB (in a
   separate build of the same modules). `Challenge` warns once (declaration uses `sorry`, as
   intended).
2. `lake env lean scripts/CheckAxioms.lean`:
   `'Cage87.exists_regular_girth_seven' depends on axioms: [propext, Classical.choice, Quot.sound]`.
3. `lake comparator` needs bubblewrap (Linux namespaces) and does not run on macOS; the
   `--inadvisably-no-sandbox` mode was not used. Palomar's preflight workflow runs it on Linux after a
   push. In its place, steps 4 and 6 were run by hand.
4. Statement comparison: every constant reachable from the type of the compared theorem (following
   definition values, not proofs) was printed with `pp.all` and hashes in the Challenge and in the
   Solution environment. The two outputs (1 root, 689 constants) are identical.
5. Controls (`RedControl.lean`): one edge moved (`{0, 384}` to `{0, 1}`, so vertex 384 has degree 7
   and vertex 1 degree 9): `wf_ok` fails. A degree-preserving switch (`{0, 384}`, `{398, 67}` to
   `{0, 398}`, `{384, 67}`, which closes the triangle `0, 14, 398`): the graph is still simple and
   8-regular (`wfOk` passes), but the branch check fails at vertex 0 and over all vertices. The
   unchanged vertex 0 passes.
6. Kernel replays: `leanexport` wrote both modules with the compared theorem as target; the Solution
   export (26.0 MB) was replayed through every kernel bundled with the toolchain (each run would have
   been stopped had it passed 7 GB of memory; none did):

   ```
   leanchecker            rc 0    45 s   1.2 GB
   nanoda                 rc 0    14 s   3.7 GB
   con-ron --jobs=1       rc 0    28 s   1.2 GB   accepted 5918 declarations (--verified)
   leanchecker-paranoid   rc 0    64 s   1.4 GB
   lean4lean              rc 0    54 s   1.2 GB   checked 5915 declarations
   con-leche              rc 0   151 s   5.5 GB   accepted 5918 declarations (--verified)
   ```

   NanoDa with unpermitted axioms as a hard error: Solution export exit 0; Challenge export exit 1
   (`export file declares unpermitted axiom "sorryAx"`), as it should. `Lean.ofReduceBool` does not
   occur in the Solution export. SHA-256 of the exports: `solution.ndjson`
   `fa9a01ef2bfc080574f30203ad5bffec8643e0ae149d2070935a5c4765bc09c9`, `challenge.ndjson`
   `b2280ebdb80268ef7a193680066b141b175f547477b24a05d9913aa4297c72bd`.

## What remains

- Palomar's mechanical preflight (the workflow above, on GitHub's Linux runners) has not run: it needs
  the repository to be public on GitHub.
- No review outside Quantavane's agents.
- Not formalized: the general construction for every odd prime power `q ≥ 7` and its proof; the
  cage number `n(k, g)` as a definition.
