import OpenProblems.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

/-!
# The three-colour triangle Ramsey number `R(3;3) = R(3,3,3) = 17`

Source: `formal-conjectures`, `ErdosProblems/183.lean`, which defines
`ForcesMonochromaticTriangle n k` (every `k`-colouring of the edges of `K_n`, as a Mathlib
`TopEdgeLabeling`, has a monochromatic triangle) and `multicolourTriangleRamsey k` as the least
such `n`. The catalogue only states the asymptotics of `R(3;k)`; here we compute the first
non-trivial value, the theorem of Greenwood and Gleason (1955):

* upper bound: a vertex of `K_17` has at least `6` neighbours of one colour; inside them, the
  other two colours form a 2-colouring of `K_6`, and `R(3,3) = 6` finishes;
* lower bound: the Greenwood–Gleason colouring of `K_16`, with vertices `GF(16)` and the colour
  of `{x, y}` the class of `x - y` modulo the cubes, checked by kernel computation.
-/

namespace OpenProblems.TriangleRamsey

open Finset SimpleGraph OpenProblems.Ramsey

/-- Verbatim from formal-conjectures (with `C.CliqueFree 3` unfolded to its definition
`∀ i, (C.labelGraph i).CliqueFree 3`). -/
def ForcesMonochromaticTriangle (n k : ℕ) : Prop :=
  ∀ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), ¬ ∀ i, (C.labelGraph i).CliqueFree 3

/-- Verbatim from formal-conjectures. -/
noncomputable def multicolourTriangleRamsey (k : ℕ) : ℕ :=
  sInf {n : ℕ | ForcesMonochromaticTriangle n k}

/-! ### Upper bound -/

theorem adj_cases {n : ℕ} (C : TopEdgeLabeling (Fin n) (Fin 3)) {i j k : Fin 3}
    (hcov : ∀ c : Fin 3, c = i ∨ c = j ∨ c = k) {x y : Fin n} (hxy : x ≠ y)
    (hj : ¬ (C.labelGraph j).Adj x y) :
    (C.labelGraph i).Adj x y ∨ (C.labelGraph k).Adj x y := by
  rcases hcov (C.get x y hxy) with h | h | h
  · exact Or.inl ((TopEdgeLabeling.labelGraph_adj x y).2 ⟨hxy, h⟩)
  · exact absurd ((TopEdgeLabeling.labelGraph_adj x y).2 ⟨hxy, h⟩) hj
  · exact Or.inr ((TopEdgeLabeling.labelGraph_adj x y).2 ⟨hxy, h⟩)

/-- Six common `i`-neighbours of a vertex force a monochromatic triangle. -/
theorem key {n : ℕ} (C : TopEdgeLabeling (Fin n) (Fin 3))
    (hfree : ∀ c, (C.labelGraph c).CliqueFree 3) {i j k : Fin 3}
    (hcov : ∀ c : Fin 3, c = i ∨ c = j ∨ c = k) (v : Fin n) (s : Finset (Fin n))
    (hs : 6 ≤ #s) (hv : ∀ w ∈ s, (C.labelGraph i).Adj v w) : False := by
  rcases ram_3_3 (Fin n) (C.labelGraph j) s hs with ⟨t, -, ht⟩ | ⟨t, hts, ht⟩
  · exact hfree j t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.1 ht.2
  rw [is3Clique_triple_iff] at ht
  obtain ⟨h1, h2, h3⟩ := ht
  rw [compl_adj] at h1 h2 h3
  have hvx := hv x (hts (by simp))
  have hvy := hv y (hts (by simp))
  have hvz := hv z (hts (by simp))
  have tri : ∀ a b, (C.labelGraph i).Adj v a → (C.labelGraph i).Adj v b →
      (C.labelGraph i).Adj a b → False := fun a b ha hb hab =>
    hfree i {v, a, b} (is3Clique_triple_iff.2 ⟨ha, hb, hab⟩)
  rcases adj_cases C hcov h1.1 h1.2 with e1 | e1
  · exact tri x y hvx hvy e1
  rcases adj_cases C hcov h2.1 h2.2 with e2 | e2
  · exact tri x z hvx hvz e2
  rcases adj_cases C hcov h3.1 h3.2 with e3 | e3
  · exact tri y z hvy hvz e3
  exact hfree k {x, y, z} (is3Clique_triple_iff.2 ⟨e1, e2, e3⟩)

theorem forces_17 : ForcesMonochromaticTriangle 17 3 := by
  intro C hfree
  let N : Fin 3 → Finset (Fin 17) := fun c => univ.filter fun w => (C.labelGraph c).Adj 0 w
  have hcover : univ.erase (0 : Fin 17) ⊆ N 0 ∪ N 1 ∪ N 2 := by
    intro w hw
    have hw0 : (0 : Fin 17) ≠ w := (ne_of_mem_erase hw).symm
    have hadj : (C.labelGraph (C.get 0 w hw0)).Adj 0 w :=
      (TopEdgeLabeling.labelGraph_adj 0 w).2 ⟨hw0, rfl⟩
    generalize C.get 0 w hw0 = c at hadj
    have hc : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
    simp only [mem_union, N, mem_filter, mem_univ, true_and]
    rcases hc with rfl | rfl | rfl
    · exact Or.inl (Or.inl hadj)
    · exact Or.inl (Or.inr hadj)
    · exact Or.inr hadj
  have hcard : 16 ≤ #(N 0) + #(N 1) + #(N 2) := by
    have h1 := card_le_card hcover
    have h2 := card_union_le (N 0 ∪ N 1) (N 2)
    have h3 := card_union_le (N 0) (N 1)
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h1
    omega
  have hN : ∀ c, ∀ w ∈ N c, (C.labelGraph c).Adj 0 w := fun c w hw => (mem_filter.1 hw).2
  by_cases h0 : 6 ≤ #(N 0)
  · exact key C hfree (i := 0) (j := 1) (k := 2) (by decide) 0 _ h0 (hN 0)
  by_cases h1 : 6 ≤ #(N 1)
  · exact key C hfree (i := 1) (j := 0) (k := 2) (by decide) 0 _ h1 (hN 1)
  have h2 : 6 ≤ #(N 2) := by omega
  exact key C hfree (i := 2) (j := 0) (k := 1) (by decide) 0 _ h2 (hN 2)

/-! ### Lower bound: the Greenwood–Gleason colouring -/

/-- Discrete logarithms in `GF(16) = 𝔽₂[x]/(x⁴+x+1)` (elements as 4-bit numbers, base `x`);
the entry for `0` is a placeholder. -/
def logTab : List ℕ := [0, 0, 1, 4, 2, 8, 5, 10, 3, 14, 9, 7, 6, 13, 11, 12]

/-- The colour of `{a, b}`: the class of `a + b` (= `a - b` in characteristic 2) modulo
the subgroup of cubes. -/
def col (a b : ℕ) : ℕ := logTab.getD (a ^^^ b) 0 % 3

theorem col_comm (a b : ℕ) : col a b = col b a := by
  unfold col; rw [Nat.xor_comm]

theorem col_lt (a b : ℕ) : col a b < 3 := Nat.mod_lt _ (by norm_num)

def GG : TopEdgeLabeling (Fin 16) (Fin 3) :=
  EdgeLabeling.mk (fun x y _ => ⟨col x y, col_lt _ _⟩)
    (fun x y _ => by simp only [col_comm])

theorem GG_adj (c : Fin 3) (x y : Fin 16) :
    (GG.labelGraph c).Adj x y → decide (col x y = c.val) = true := by
  rw [TopEdgeLabeling.labelGraph_adj]
  rintro ⟨H, hc⟩
  rw [← hc]
  simp [GG, EdgeLabeling.get_mk]

theorem GG_check : ∀ c : Fin 3, free3 (fun a b => decide (col a b = c.val)) 16 = true := by
  decide +kernel

theorem not_forces_16 : ¬ ForcesMonochromaticTriangle 16 3 := fun h =>
  h GG fun c => cliqueFree_of_free3 _ _ (GG_adj c) (GG_check c)

/-- Restricting a colouring to fewer vertices. -/
theorem not_forces_of_le {m n k : ℕ} (h : ¬ ForcesMonochromaticTriangle m k) (hnm : n ≤ m) :
    ¬ ForcesMonochromaticTriangle n k := by
  intro hn
  unfold ForcesMonochromaticTriangle at h
  push_neg at h
  obtain ⟨C, hC⟩ := h
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  refine hn (C.pullback f) fun c t ht => hC c (t.map f) ?_
  rw [isNClique_iff] at ht ⊢
  refine ⟨?_, by simp [ht.2]⟩
  intro x hx y hy hne
  obtain ⟨a, ha, rfl⟩ := mem_map.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_map.1 hy
  have hab : a ≠ b := fun e => hne (e ▸ rfl)
  have := ht.1 ha hb hab
  rw [TopEdgeLabeling.labelGraph_adj] at this ⊢
  obtain ⟨H, hc⟩ := this
  exact ⟨fun e => H (f.injective e), hc⟩

/-- **Greenwood–Gleason (1955)**: `R(3,3,3) = 17`, with the catalogue's definitions. -/
theorem multicolourTriangleRamsey_three : multicolourTriangleRamsey 3 = 17 := by
  apply le_antisymm (Nat.sInf_le forces_17)
  apply le_csInf ⟨17, forces_17⟩
  intro n hn
  by_contra hlt
  exact not_forces_of_le not_forces_16 (by omega) hn

end OpenProblems.TriangleRamsey
