module

public import Cage87.Check
public import Cage87.Data
public import Cage87.Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# From the kernel checks to the graph

* `G` is the graph on `Fin 768` whose adjacency is given by the lists stored in `adj`; `wf_ok`
  makes it a simple graph (`nb_prop`), and every vertex has degree 8 (`degree_eq`).
* `branch_disjoint`: by `vertices_ok`, for two different neighbours `x ≠ y` of a vertex `v`, the
  branches of `v` through `x` and through `y` have no vertex in common.
* `seven_le_length`: a cycle of length `ℓ ≤ 6` through `v = v₀, v₁, …, v_{ℓ-1}` would put its
  vertex `v_{⌊ℓ/2⌋}` in the branch of `v₀` through `v₁` and in the branch through `v_{ℓ-1}`, by the
  two halves of the cycle (non-backtracking walks of lengths `⌊ℓ/2⌋` and `⌈ℓ/2⌉`, at most 3).
* `cycle7`: an explicit cycle of length 7. So the girth is 7 (`girth_eq`).
-/

namespace Cage87

open SimpleGraph

/-! ## The checks, read as statements -/

theorem nodup_of_nodupB : ∀ l : List Nat, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hx => ?_, nodup_of_nodupB l h.2⟩
    have := List.contains_iff_mem.mpr hx
    rw [h.1] at this
    exact Bool.false_ne_true this

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem wfV_of_wfOk (h : wfOk adj 768 8 = true) (v : Nat) (hv : v < 768) : wfV adj 768 8 v = true := by
  simp only [wfOk, List.all_eq_true, List.mem_range] at h
  exact h v hv

section
variable {v : Nat} (hv : v < 768)
include hv

theorem nb_length : (nb adj v).length = 8 := by
  have h := wfV_of_wfOk wf_ok v hv
  simp only [wfV, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.1

theorem nb_nodup : (nb adj v).Nodup := by
  have h := wfV_of_wfOk wf_ok v hv
  simp only [wfV, Bool.and_eq_true] at h
  exact nodup_of_nodupB _ h.1.2

theorem nb_prop {x : Nat} (hx : x ∈ nb adj v) : x < 768 ∧ x ≠ v ∧ v ∈ nb adj x := by
  have h := wfV_of_wfOk wf_ok v hv
  simp only [wfV, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 x hx
  simp only [Nat.blt_eq, Bool.not_eq_true', List.contains_iff_mem] at this
  refine ⟨this.1.1, fun e => ?_, this.2⟩
  have h' := this.1.2
  rw [e] at h'
  simp at h'

end

/-! ## The graph -/

/-- The graph: `u` and `v` are adjacent when `v` is listed among the neighbours of `u`. -/
noncomputable def G : SimpleGraph (Fin 768) where
  Adj u v := v.val ∈ nb adj u.val
  symm := ⟨fun u _ h => (nb_prop u.2 h).2.2⟩
  loopless := ⟨fun u h => (nb_prop u.2 h).2.1 rfl⟩

@[simp] theorem G_adj (u v : Fin 768) : G.Adj u v ↔ v.val ∈ nb adj u.val := Iff.rfl

noncomputable instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (v.val ∈ nb adj u.val))

theorem degree_eq (v : Fin 768) : G.degree v = 8 := by
  rw [← card_neighborFinset_eq_degree]
  have h : (G.neighborFinset v).map ⟨Fin.val, Fin.val_injective⟩ = (nb adj v.val).toFinset := by
    ext z
    simp only [Finset.mem_map, mem_neighborFinset, G_adj, Function.Embedding.coeFn_mk,
      List.mem_toFinset]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hz; exact ⟨⟨z, (nb_prop v.2 hz).1⟩, hz, rfl⟩
  rw [← Finset.card_map, h, List.toFinset_card_of_nodup (nb_nodup v.2), nb_length v.2]

theorem isRegular : G.IsRegularOfDegree 8 := degree_eq

/-! ## Branches -/

theorem testBit_maskOf (z : Nat) : ∀ l : List Nat, (maskOf l).testBit z = true ↔ z ∈ l
  | [] => by simp [maskOf]
  | x :: l => by
    simp only [maskOf]
    show (1 <<< x ||| maskOf l).testBit z = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_maskOf z l, Nat.one_shiftLeft, Nat.testBit_two_pow,
      List.mem_cons, decide_eq_true_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem pairwise_of_pwDisj : ∀ ms : List Nat, pwDisj ms = true → ms.Pairwise (fun a b => a &&& b = 0)
  | [], _ => List.Pairwise.nil
  | m :: ms, h => by
    simp only [pwDisj, Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] at h
    exact List.Pairwise.cons (fun m' hm' => h.1 m' hm') (pairwise_of_pwDisj ms h.2)

theorem pairwise_rel {α : Type*} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ {x y : α}, x ∈ l → y ∈ l → x ≠ y → R x y ∨ R y x
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, h, x, y, hx, hy, hxy => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · exact absurd rfl hxy
    · exact Or.inl (h.1 y hy')
    · exact Or.inr (h.1 x hx')
    · exact pairwise_rel h.2 hx' hy' hxy

theorem branch_disjoint {v x y z : Nat} (hv : v < 768) (hx : x ∈ nb adj v) (hy : y ∈ nb adj v)
    (hxy : x ≠ y) (hzx : z ∈ branch adj v x) (hzy : z ∈ branch adj v y) : False := by
  have hp := pairwise_of_pwDisj _ (vertices_ok v hv)
  rw [List.pairwise_map] at hp
  have key : ∀ a b, brMask adj v a &&& brMask adj v b = 0 → z ∈ branch adj v a →
      z ∈ branch adj v b → False := by
    intro a b hab ha hb
    have h1 := (testBit_maskOf z _).mpr ha
    have h2 := (testBit_maskOf z _).mpr hb
    have : (brMask adj v a &&& brMask adj v b).testBit z = true := by
      rw [Nat.testBit_and]; simp only [brMask] at h1 h2 ⊢; rw [h1, h2]; rfl
    rw [hab] at this
    simp at this
  rcases pairwise_rel hp hx hy hxy with h | h
  · exact key x y h hzx hzy
  · exact key y x h hzy hzx

theorem mem_branch_one (v x : Nat) : x ∈ branch adj v x := List.mem_cons_self

theorem mem_branch_two {v x y : Nat} (hy : y ∈ nb adj x) (hyv : y ≠ v) : y ∈ branch adj v x := by
  simp only [branch, List.mem_cons, List.mem_append, List.mem_filter, Bool.not_eq_true']
  exact Or.inr (Or.inl ⟨hy, beq_false_of_ne hyv⟩)

theorem mem_branch_three {v x y z : Nat} (hy : y ∈ nb adj x) (hyv : y ≠ v) (hz : z ∈ nb adj y)
    (hzx : z ≠ x) : z ∈ branch adj v x := by
  simp only [branch, List.mem_cons, List.mem_append, List.mem_filter, List.mem_flatMap,
    Bool.not_eq_true']
  exact Or.inr (Or.inr ⟨y, ⟨hy, beq_false_of_ne hyv⟩, hz, beq_false_of_ne hzx⟩)

/-! ## The girth -/

/-- Every cycle of `G` has length at least 7. -/
theorem seven_le_length {a : Fin 768} (w : G.Walk a a) (hw : w.IsCycle) : 7 ≤ w.length := by
  by_contra hlt
  have h3 := hw.three_le_length
  have hadj : ∀ i < w.length, (w.getVert (i + 1)).val ∈ nb adj (w.getVert i).val :=
    fun i hi => w.adj_getVert_succ hi
  have hadj' : ∀ i < w.length, (w.getVert i).val ∈ nb adj (w.getVert (i + 1)).val :=
    fun i hi => (w.adj_getVert_succ hi).symm
  have hinj : ∀ i j, i ≤ w.length - 1 → j ≤ w.length - 1 →
      (w.getVert i).val = (w.getVert j).val → i = j :=
    fun i j hi hj h => hw.getVert_injOn' hi hj (Fin.ext h)
  have h0 : (w.getVert 0).val = a.val := by rw [Walk.getVert_zero]
  have hl : (w.getVert w.length).val = a.val := by rw [Walk.getVert_length]
  have hv := a.2
  generalize w.length = l at *
  have hx : (w.getVert 1).val ∈ nb adj a.val := h0 ▸ hadj 0 (by omega)
  have hy : (w.getVert (l - 1)).val ∈ nb adj a.val := by
    have := hadj' (l - 1) (by omega)
    rwa [show l - 1 + 1 = l by omega, hl] at this
  have hxy : (w.getVert 1).val ≠ (w.getVert (l - 1)).val := fun h => by
    have := hinj 1 (l - 1) (by omega) (by omega) h; omega
  have hne : ∀ i j, i ≤ l - 1 → j ≤ l - 1 → i ≠ j → (w.getVert i).val ≠ (w.getVert j).val :=
    fun i j hi hj hij h => hij (hinj i j hi hj h)
  have hna : ∀ i, 1 ≤ i → i ≤ l - 1 → (w.getVert i).val ≠ a.val := fun i h1 h2 h => by
    have := hinj i 0 h2 (by omega) (h.trans h0.symm); omega
  interval_cases l
  · -- l = 3: v₁ is in both branches
    exact branch_disjoint hv hx hy hxy (mem_branch_one _ _)
      (mem_branch_two (hadj' 1 (by omega)) (hna 1 (by omega) (by omega)))
  · -- l = 4: v₂
    exact branch_disjoint hv hx hy hxy (mem_branch_two (hadj 1 (by omega)) (hna 2 (by omega) (by omega)))
      (mem_branch_two (hadj' 2 (by omega)) (hna 2 (by omega) (by omega)))
  · -- l = 5: v₂, through v₁ and through v₄, v₃
    exact branch_disjoint hv hx hy hxy (mem_branch_two (hadj 1 (by omega)) (hna 2 (by omega) (by omega)))
      (mem_branch_three (hadj' 3 (by omega)) (hna 3 (by omega) (by omega)) (hadj' 2 (by omega))
        (hne 2 4 (by omega) (by omega) (by omega)))
  · -- l = 6: v₃, through v₁, v₂ and through v₅, v₄
    exact branch_disjoint hv hx hy hxy
      (mem_branch_three (hadj 1 (by omega)) (hna 2 (by omega) (by omega)) (hadj 2 (by omega))
        (hne 3 1 (by omega) (by omega) (by omega)))
      (mem_branch_three (hadj' 4 (by omega)) (hna 4 (by omega) (by omega)) (hadj' 3 (by omega))
        (hne 3 5 (by omega) (by omega) (by omega)))

/-- A cycle of length 7: `0, 14, 398, 67, 468, 83, 387`. -/
def cycle7 : G.Walk 0 0 :=
  Walk.cons (v := 14) (by decide +kernel) <| Walk.cons (v := 398) (by decide +kernel) <|
    Walk.cons (v := 67) (by decide +kernel) <| Walk.cons (v := 468) (by decide +kernel) <|
      Walk.cons (v := 83) (by decide +kernel) <| Walk.cons (v := 387) (by decide +kernel) <|
        Walk.cons (v := 0) (by decide +kernel) Walk.nil

theorem cycle7_isCycle : cycle7.IsCycle := by
  rw [cycle7, Walk.cons_isCycle_iff, Walk.isPath_def]
  constructor
  · decide +kernel
  · decide +kernel

theorem girth_eq : G.girth = 7 := by
  have h1 : G.egirth ≤ 7 := cycle7_isCycle.egirth_le_length.trans (by rfl)
  have h2 : 7 ≤ G.egirth := le_egirth.mpr fun a w hw => by exact_mod_cast seven_le_length w hw
  rw [girth, le_antisymm h1 h2]
  rfl

end Cage87
