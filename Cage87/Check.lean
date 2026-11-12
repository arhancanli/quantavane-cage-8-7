module

@[expose] public section

/-!
# The finite checks, written for evaluation by Lean's kernel

A graph on the vertices `0, …, n - 1` is given by its adjacency lists, stored in a binary trie
`adj` so that the kernel finds the list of a vertex in a few steps (`nb adj v`, the neighbours of
`v`). The checks, all evaluated by Lean's kernel:

* `wfOk adj n d`: for each `v < n`, the list has `d` distinct entries below `n`, does not contain
  `v`, and every listed neighbour lists `v` back.
* `vertexOk adj v`: the *branches* of `v` are pairwise disjoint. The branch of `v` through a
  neighbour `x` (`branch adj v x`) is `x`, the neighbours `y ≠ v` of `x`, and the neighbours
  `z ≠ x` of those `y`: the ends of the non-backtracking walks of length 1, 2 and 3 that start
  with the edge `v x`. Sets of vertices are bitmasks (`maskOf`), so disjointness is one `land`.

The meaning of the checks is in `Cage87.Bridge`. All functions use structural recursion and the
`Nat` primitives, which the kernel evaluates with GMP.
-/

namespace Cage87

/-- A binary trie of adjacency lists, indexed by the bits of the vertex, lowest bit first. -/
inductive Trie where
  | leaf : List Nat → Trie
  | node : Trie → Trie → Trie

/-- The list stored at `v`. -/
def Trie.find : Trie → Nat → List Nat
  | .leaf l, _ => l
  | .node a b, v => cond (Nat.beq (Nat.mod v 2) 0) (a.find (Nat.div v 2)) (b.find (Nat.div v 2))

/-- The neighbours of vertex `v`. -/
def nb (adj : Trie) (v : Nat) : List Nat := adj.find v

/-- The bitmask of a list of vertices. -/
def maskOf : List Nat → Nat
  | [] => 0
  | x :: l => Nat.lor (Nat.shiftLeft 1 x) (maskOf l)

/-- The branch of `v` through its neighbour `x`. -/
def branch (adj : Trie) (v x : Nat) : List Nat :=
  let ys := (nb adj x).filter (fun y => !(Nat.beq y v))
  x :: (ys ++ ys.flatMap (fun y => (nb adj y).filter (fun z => !(Nat.beq z x))))

/-- The bitmask of a branch. -/
def brMask (adj : Trie) (v x : Nat) : Nat := maskOf (branch adj v x)

/-- The masks are pairwise disjoint. -/
def pwDisj : List Nat → Bool
  | [] => true
  | m :: ms => ms.all (fun m' => Nat.beq (Nat.land m m') 0) && pwDisj ms

/-- The branches of `v` are pairwise disjoint. -/
def vertexOk (adj : Trie) (v : Nat) : Bool := pwDisj ((nb adj v).map (brMask adj v))

/-- The vertices `lo, …, lo + c - 1` pass `vertexOk`. -/
def verticesOk (adj : Trie) : Nat → Nat → Bool
  | _, 0 => true
  | lo, c + 1 => vertexOk adj lo && verticesOk adj (lo + 1) c

/-- No entry repeats. -/
def nodupB : List Nat → Bool
  | [] => true
  | x :: l => !(l.contains x) && nodupB l

/-- The adjacency list of `v` is well formed. -/
def wfV (adj : Trie) (n d v : Nat) : Bool :=
  Nat.beq (nb adj v).length d && nodupB (nb adj v) &&
    (nb adj v).all (fun x => Nat.blt x n && !(Nat.beq x v) && (nb adj x).contains v)

/-- All adjacency lists are well formed. -/
def wfOk (adj : Trie) (n d : Nat) : Bool := (List.range n).all (wfV adj n d)

/-- A successful chunk check covers each of its vertices. -/
theorem verticesOk_mem (adj : Trie) : ∀ (lo c : Nat), verticesOk adj lo c = true →
    ∀ v, lo ≤ v → v < lo + c → vertexOk adj v = true := by
  intro lo c
  induction c generalizing lo with
  | zero => intro _ v h1 h2; omega
  | succ c ih =>
    intro h v h1 h2
    simp only [verticesOk, Bool.and_eq_true] at h
    by_cases hv : v = lo
    · exact hv ▸ h.1
    · exact ih (lo + 1) h.2 v (by omega) (by omega)

end Cage87
