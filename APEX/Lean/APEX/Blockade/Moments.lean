import APEX.Blockade.Count
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Range-`r` blockade: polynomial identities and the second spectral moment

Notation: `D_r = 1 − z − z^{r+1}`, `B_r = 1 + z + … + z^r`, `S_r = 1 + z + … + z^{r−1}`.

* `ident_a` (any commutative ring, all `r`): `D_r · S_r + z^r · B_r = 1`;
  `ident_a_poly` is its instance in `ℤ[X]`.
* `ident_b` (all `r`): `(z^r + … + z^{2r−1}) · D_r + z^{2r} · B_r = z^r`; `ident_b_poly` in `ℤ[X]`.
* `adjMat r n` : the adjacency matrix of the range-`r` constrained hypercube on `C r n`
  (two admissible words are adjacent iff one is obtained from the other by flipping
  exactly one bit, `Adj`).
* `trace_sq_eq` : `Tr (adjMat r n)^2 = 2 · e r n`, where `e r n` is the total number of `1`s
  over all admissible words of length `n` (i.e. the number of edges); proved by the
  involution `(w, i) ↦ (flip w i, i)`.
* `e_rec`, `e_of_le` : `e (n+r+1) = e (n+r) + e n + a n` and `e n = n` for `n ≤ r`,
  derived combinatorially from the first-letter decomposition.
* `second_moment_series` (all `r`, including `r = 0`, the hypercube):
  `(∑ₙ Tr (adjMat r n)^2 zⁿ) · (1 − z − z^{r+1})² = 2z` as formal power series over `ℤ`.

Not proved here: the fourth moment and higher moments.  `Conj4` and `ConjGeneral` below are
*statements* (definitions of propositions), not theorems; the docstring of `ConjGeneral` lists
what changes in the PXP `Good`/`GoodT`/`GoodR` induction.
-/

namespace APEX.Blockade

open Finset

/-! ### 1. Polynomial identities -/

section Ident

variable {R : Type*} [CommRing R]

/-- Identity (a): `D_r · (∑_{g<r} x^g) + x^r · B_r = 1`. -/
theorem ident_a (x : R) (r : ℕ) :
    (1 - x - x ^ (r + 1)) * (∑ g ∈ range r, x ^ g) + x ^ r * (∑ i ∈ range (r + 1), x ^ i) = 1 := by
  have h := mul_neg_geom_sum x r
  rw [sum_range_succ]
  linear_combination (1 + x ^ r) * h

/-- Identity (b): `(∑_{g=r}^{2r-1} x^g) · D_r + x^{2r} · B_r = x^r`. -/
theorem ident_b (x : R) (r : ℕ) :
    (∑ g ∈ Ico r (2 * r), x ^ g) * (1 - x - x ^ (r + 1)) + x ^ (2 * r) * (∑ i ∈ range (r + 1), x ^ i)
      = x ^ r := by
  have hs : (∑ g ∈ Ico r (2 * r), x ^ g) = x ^ r * ∑ g ∈ range r, x ^ g := by
    rw [sum_Ico_eq_sum_range, show 2 * r - r = r by omega, mul_sum]
    refine sum_congr rfl (fun g _ => by rw [pow_add])
  rw [hs, show 2 * r = r + r by omega, pow_add]
  linear_combination x ^ r * ident_a x r

open Polynomial in
theorem ident_a_poly (r : ℕ) :
    (1 - X - X ^ (r + 1) : ℤ[X]) * (∑ g ∈ range r, X ^ g) + X ^ r * (∑ i ∈ range (r + 1), X ^ i) = 1 :=
  ident_a X r

open Polynomial in
theorem ident_b_poly (r : ℕ) :
    (∑ g ∈ Ico r (2 * r), (X : ℤ[X]) ^ g) * (1 - X - X ^ (r + 1)) +
      X ^ (2 * r) * (∑ i ∈ range (r + 1), X ^ i) = X ^ r :=
  ident_b X r

end Ident

/-! ### 2. The constrained hypercube and its adjacency matrix -/

/-- Flip the bit at position `i`. -/
def flip (w : List Bool) (i : ℕ) : List Bool := w.set i (!(w.getD i false))

/-- Adjacency: `v` arises from `u` by flipping exactly one position `i < |u|`. -/
def Adj (u v : List Bool) : Prop := ∃ i ∈ range u.length, v = flip u i

instance : DecidableRel Adj := fun u v => by unfold Adj; infer_instance

/-- Vertices: admissible words of length `n`. -/
abbrev V (r n : ℕ) := {w : List Bool // w ∈ C r n}

/-- Adjacency matrix of the range-`r` constrained hypercube (PXP-type Hamiltonian with
unit couplings on the range-`r` blockade subspace of an open chain of `n` sites). -/
def adjMat (r n : ℕ) : Matrix (V r n) (V r n) ℤ := Matrix.of fun u v => if Adj u.1 v.1 then 1 else 0

lemma length_flip (w : List Bool) (i : ℕ) : (flip w i).length = w.length := by simp [flip]

lemma getD_flip_self {w : List Bool} {i : ℕ} (h : i < w.length) :
    (flip w i).getD i false = !(w.getD i false) := by
  simp [flip, List.getD_eq_getElem?_getD, h]

lemma getD_flip_ne (w : List Bool) {i j : ℕ} (h : i ≠ j) :
    (flip w i).getD j false = w.getD j false := by
  simp [flip, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

lemma flip_flip {w : List Bool} {i : ℕ} (h : i < w.length) : flip (flip w i) i = w := by
  apply List.ext_getElem?
  intro j
  have hl := length_flip w i
  by_cases hij : i = j
  · subst hij
    show ((flip w i).set i _)[i]? = _
    rw [List.getElem?_set_self (by rw [length_flip]; exact h), getD_flip_self h, Bool.not_not,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  · simp [flip, List.getElem?_set_ne hij]

lemma flip_inj {w : List Bool} {i j : ℕ} (hi : i < w.length) (h : flip w i = flip w j) : i = j := by
  by_contra hij
  have h1 := getD_flip_self hi
  rw [h, getD_flip_ne w (Ne.symm hij)] at h1
  cases w.getD i false <;> simp at h1

/-- Lowering a `1` to `0` preserves admissibility. -/
lemma adm_set_false {r : ℕ} : ∀ {w : List Bool} {i : ℕ}, Adm r w → Adm r (w.set i false)
  | [], _, h => by simpa using h
  | b :: l, 0, h => by
      cases b <;> simp only [List.set_cons_zero, Adm] at h ⊢
      · exact h
      · exact h.2
  | b :: l, i + 1, h => by
      cases b <;> simp only [List.set_cons_succ, Adm] at h ⊢
      · exact adm_set_false h
      · refine ⟨fun x hx => ?_, adm_set_false h.2⟩
        rw [List.take_set] at hx
        rcases List.mem_or_eq_of_mem_set hx with hx | hx
        · exact h.1 x hx
        · exact hx

lemma adm_flip_of_true {r : ℕ} {w : List Bool} {i : ℕ} (hw : Adm r w) (hi : w.getD i false = true) :
    Adm r (flip w i) := by
  unfold flip; rw [hi]; exact adm_set_false hw

lemma adj_symm {u v : List Bool} (h : Adj u v) : Adj v u := by
  obtain ⟨i, hi, rfl⟩ := h
  rw [mem_range] at hi
  exact ⟨i, by rw [mem_range, length_flip]; exact hi, (flip_flip hi).symm⟩

/-- Number of `1`s at index set: `count true w = #{i < |w| : w_i = 1}`. -/
lemma count_true_eq (w : List Bool) :
    w.count true = ((range w.length).filter (fun i => w.getD i false = true)).card := by
  induction w with
  | nil => simp
  | cons b l ih =>
    rw [card_filter, List.length_cons, sum_range_succ', List.count_cons, ih, card_filter]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    cases b <;> simp

lemma sum_card_filter_eq {α β : Type*} (s : Finset α) (t : Finset β) (p : α → β → Prop)
    [∀ a b, Decidable (p a b)] :
    ∑ a ∈ s, (t.filter (p a)).card = ((s ×ˢ t).filter (fun x => p x.1 x.2)).card := by
  rw [card_filter, sum_product]
  exact sum_congr rfl (fun a _ => by rw [card_filter])

/-- Total number of `1`s over admissible words of length `n` (= number of edges). -/
def e (r n : ℕ) : ℕ := ∑ w ∈ C r n, w.count true

/-- Degree of a vertex: number of admissible single flips. -/
lemma card_adj (r n : ℕ) (u : V r n) :
    (univ.filter (fun v : V r n => Adj u.1 v.1)).card =
      ((range n).filter (fun i => Adm r (flip u.1 i))).card := by
  have hu := mem_C.1 u.2
  symm
  apply card_bij (fun i hi => (⟨flip u.1 i, mem_C.2 ⟨by rw [length_flip, hu.1],
    (mem_filter.1 hi).2⟩⟩ : V r n))
  · intro i hi
    rw [mem_filter] at hi ⊢
    exact ⟨mem_univ _, i, by rw [hu.1]; exact hi.1, rfl⟩
  · intro i hi j hj h
    have := congrArg Subtype.val h
    exact flip_inj (by rw [hu.1]; exact mem_range.1 (mem_filter.1 hi).1) this
  · intro v hv
    obtain ⟨-, i, hi, hv⟩ := mem_filter.1 hv
    rw [hu.1] at hi
    refine ⟨i, mem_filter.2 ⟨hi, ?_⟩, Subtype.ext hv.symm⟩
    rw [← hv]; exact (mem_C.1 v.2).2

theorem trace_sq_eq_sum_deg (r n : ℕ) :
    Matrix.trace (adjMat r n ^ 2) =
      ∑ w ∈ C r n, (((range n).filter (fun i => Adm r (flip w i))).card : ℤ) := by
  rw [pow_two, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, adjMat, Matrix.of_apply]
  have h1 : ∀ u v : V r n, ((if Adj u.1 v.1 then (1 : ℤ) else 0) * if Adj v.1 u.1 then 1 else 0)
      = if Adj u.1 v.1 then 1 else 0 := by
    intro u v
    by_cases h : Adj u.1 v.1
    · simp [h, adj_symm h]
    · simp [h]
  simp only [h1, sum_boole]
  simp_rw [card_adj]
  rw [univ_eq_attach]
  exact sum_attach (C r n) (fun w => (((range n).filter (fun i => Adm r (flip w i))).card : ℤ))

/-- **Tr A² = 2 · (number of edges)**. -/
theorem trace_sq_eq (r n : ℕ) : Matrix.trace (adjMat r n ^ 2) = 2 * (e r n : ℤ) := by
  rw [trace_sq_eq_sum_deg]
  -- split each degree by the value of the flipped bit
  have hsplit : ∀ w ∈ C r n, ((range n).filter (fun i => Adm r (flip w i))).card =
      ((range n).filter (fun i => w.getD i false = true)).card +
      ((range n).filter (fun i => w.getD i false = false ∧ Adm r (flip w i))).card := by
    intro w hw
    rw [← card_union_of_disjoint]
    · congr 1
      ext i
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hi, ha⟩
        cases hb : w.getD i false
        · exact Or.inr ⟨hi, rfl, ha⟩
        · exact Or.inl ⟨hi, rfl⟩
      · rintro (⟨hi, hb⟩ | ⟨hi, -, ha⟩)
        · exact ⟨hi, adm_flip_of_true (mem_C.1 hw).2 hb⟩
        · exact ⟨hi, ha⟩
    · rw [disjoint_left]
      intro i h1 h2
      rw [mem_filter] at h1 h2
      rw [h1.2] at h2
      simp at h2
  have hcount : ∀ w ∈ C r n, w.count true =
      ((range n).filter (fun i => w.getD i false = true)).card := by
    intro w hw; rw [count_true_eq, (mem_C.1 hw).1]
  -- the involution (w, i) ↦ (flip w i, i)
  have hinv : ∑ w ∈ C r n,
      ((range n).filter (fun i => w.getD i false = false ∧ Adm r (flip w i))).card =
      ∑ w ∈ C r n, ((range n).filter (fun i => w.getD i false = true)).card := by
    rw [sum_card_filter_eq, sum_card_filter_eq]
    apply card_nbij' (fun x => (flip x.1 x.2, x.2)) (fun x => (flip x.1 x.2, x.2))
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_C, mem_range] at hx ⊢
      obtain ⟨⟨⟨hl, -⟩, hi⟩, hb, ha⟩ := hx
      refine ⟨⟨⟨by rw [length_flip, hl], ha⟩, hi⟩, ?_⟩
      rw [getD_flip_self (by omega), hb]; rfl
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_C, mem_range] at hx ⊢
      obtain ⟨⟨⟨hl, ha⟩, hi⟩, hb⟩ := hx
      refine ⟨⟨⟨by rw [length_flip, hl], adm_flip_of_true ha hb⟩, hi⟩, ?_, ?_⟩
      · rw [getD_flip_self (by omega), hb]; rfl
      · rw [flip_flip (by omega)]; exact ha
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_C, mem_range] at hx
      ext1
      · exact flip_flip (by omega)
      · rfl
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_C, mem_range] at hx
      ext1
      · exact flip_flip (by omega)
      · rfl
  have : ∑ w ∈ C r n, ((range n).filter (fun i => Adm r (flip w i))).card = 2 * e r n := by
    rw [sum_congr rfl hsplit, sum_add_distrib, hinv, ← two_mul, e, sum_congr rfl hcount]
  exact_mod_cast this

/-! ### Recurrence for `e` (first-letter decomposition) -/

lemma C_succ (r n : ℕ) : C r (n + 1) = (C r n).map ⟨List.cons false, List.cons_injective⟩ ∪
    ((C r n).filter (Z r)).map ⟨List.cons true, List.cons_injective⟩ := by
  ext w
  cases w with
  | nil => simp [mem_C]
  | cons b w => cases b <;> simp [mem_C, Adm, Z] <;> tauto

lemma C_succ_disj (r n : ℕ) : Disjoint ((C r n).map ⟨List.cons false, List.cons_injective⟩)
    (((C r n).filter (Z r)).map ⟨List.cons true, List.cons_injective⟩) := by
  rw [disjoint_left]
  intro w h1 h2
  simp only [mem_map, Function.Embedding.coeFn_mk] at h1 h2
  obtain ⟨u, -, rfl⟩ := h1
  obtain ⟨v, -, hv⟩ := h2
  simp at hv

lemma e_succ (r n : ℕ) : e r (n + 1) = e r n + ∑ w ∈ (C r n).filter (Z r), w.count true
    + ((C r n).filter (Z r)).card := by
  unfold e
  rw [C_succ, sum_union (C_succ_disj r n), sum_map, sum_map]
  simp only [Function.Embedding.coeFn_mk, List.count_cons]
  simp [sum_add_distrib, add_assoc]

/-- Prepending `r` zeros. -/
def padEmb (r : ℕ) : List Bool ↪ List Bool :=
  ⟨fun l => List.replicate r false ++ l, fun _ _ h => List.append_cancel_left h⟩

@[simp] lemma padEmb_apply (r : ℕ) (l : List Bool) : padEmb r l = List.replicate r false ++ l := rfl

lemma filter_Z_of_le (r n : ℕ) : (C r (n + r)).filter (Z r) = (C r n).map (padEmb r) := by
  ext w
  simp only [mem_filter, mem_map, padEmb_apply, mem_C]
  constructor
  · rintro ⟨⟨hlen, hadm⟩, hz⟩
    obtain ⟨l, rfl⟩ := (Z_iff_of_le (by omega)).mp hz
    exact ⟨l, ⟨by simp at hlen; omega, (adm_replicate_append r r l).mp hadm⟩, rfl⟩
  · rintro ⟨l, ⟨hl, ha⟩, rfl⟩
    refine ⟨⟨by simp [hl, Nat.add_comm], (adm_replicate_append r r l).mpr ha⟩, ?_⟩
    exact (Z_iff_of_le (by simp)).mpr ⟨l, rfl⟩

lemma filter_Z_of_lt (r n : ℕ) (h : n < r) : (C r n).filter (Z r) = {List.replicate n false} := by
  ext w
  simp only [mem_filter, mem_C, mem_singleton]
  constructor
  · rintro ⟨⟨hlen, -⟩, hz⟩
    apply List.eq_replicate_iff.mpr
    refine ⟨hlen, fun x hx => hz x ?_⟩
    rwa [List.take_of_length_le (by omega)]
  · rintro rfl
    refine ⟨⟨by simp, ?_⟩, ?_⟩
    · simpa using (adm_replicate_append r n []).mpr trivial
    · intro x hx
      rw [List.take_of_length_le (by simp; omega)] at hx
      exact List.eq_of_mem_replicate hx

theorem e_zero (r : ℕ) : e r 0 = 0 := by
  simp [e, C, allL]

/-- `e r n = n` for `n ≤ r`. -/
theorem e_of_le (r n : ℕ) (h : n ≤ r) : e r n = n := by
  induction n with
  | zero => exact e_zero r
  | succ n ih =>
    rw [e_succ, ih (by omega), filter_Z_of_lt r n (by omega)]
    simp [List.count_replicate]

/-- **Edge recurrence** `e (n+r+1) = e (n+r) + e n + a n`. -/
theorem e_rec (r n : ℕ) : e r (n + r + 1) = e r (n + r) + e r n + a r n := by
  rw [e_succ, filter_Z_of_le, sum_map, card_map]
  simp only [padEmb_apply, List.count_append, List.count_replicate]
  simp [e, a]

/-! ### Power series -/

section Series

open PowerSeries

/-- `D_r` as a power series. -/
noncomputable def Dser (r : ℕ) : PowerSeries ℤ := 1 - X - X ^ (r + 1)

lemma coeff_mul_X'' (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (f * X) = if 1 ≤ n then coeff (n - 1) f else 0 := by
  simpa using coeff_mul_X_pow' f 1 n

lemma coeff_X_mul'' (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (X * f) = if 1 ≤ n then coeff (n - 1) f else 0 := by
  simpa using coeff_X_pow_mul' f 1 n

lemma coeff_mul_Dser (f : PowerSeries ℤ) (r n : ℕ) :
    coeff n (f * Dser r) = coeff n f - (if 1 ≤ n then coeff (n - 1) f else 0)
      - (if r + 1 ≤ n then coeff (n - r - 1) f else 0) := by
  rw [Dser, mul_sub, mul_sub, mul_one, map_sub, map_sub, coeff_mul_X'', coeff_mul_X_pow']
  congr 2

lemma coeff_geom (r n : ℕ) : coeff n (∑ i ∈ range r, (X : PowerSeries ℤ) ^ i) =
    if n < r then 1 else 0 := by
  rw [map_sum]
  simp only [coeff_X_pow]
  rw [sum_ite_eq]
  simp

lemma series_a (r : ℕ) :
    PowerSeries.mk (fun n => (a r n : ℤ)) * Dser r = ∑ i ∈ range (r + 1), (X : PowerSeries ℤ) ^ i := by
  ext n
  rw [coeff_mul_Dser, coeff_geom]
  simp only [coeff_mk]
  have := gf_coeff r n
  convert this using 2
  omega

lemma series_e (r : ℕ) :
    PowerSeries.mk (fun n => (e r n : ℤ)) * Dser r =
      X * (∑ i ∈ range r, (X : PowerSeries ℤ) ^ i) + X ^ (r + 1) * PowerSeries.mk (fun n => (a r n : ℤ)) := by
  ext n
  rw [coeff_mul_Dser, map_add, coeff_X_mul'', coeff_X_pow_mul']
  simp only [coeff_mk]
  rcases Nat.lt_or_ge r n with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + r + 1 := ⟨n - r - 1, by omega⟩
    rw [if_pos (show 1 ≤ k + r + 1 by omega), if_pos (show r + 1 ≤ k + r + 1 by omega),
      if_pos (show 1 ≤ k + r + 1 by omega), if_pos (show r + 1 ≤ k + r + 1 by omega),
      coeff_geom, if_neg (show ¬ (k + r + 1 - 1 < r) by omega),
      show k + r + 1 - 1 = k + r by omega, show k + r + 1 - r - 1 = k by omega, e_rec]
    rw [show k + r + 1 - (r + 1) = k by omega]
    push_cast; ring
  · rw [if_neg (show ¬ (r + 1 ≤ n) by omega), if_neg (show ¬ (r + 1 ≤ n) by omega), e_of_le r n h]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_pos (show 1 ≤ n by omega), if_pos (show 1 ≤ n by omega), e_of_le r (n - 1) (by omega),
        coeff_geom, if_pos (by omega)]
      push_cast [Nat.cast_sub hn]; ring

/-- Generating function of the edge numbers: `(∑ eₙ zⁿ) · D_r² = z`. -/
theorem series_e_sq (r : ℕ) :
    PowerSeries.mk (fun n => (e r n : ℤ)) * Dser r ^ 2 = X := by
  rw [pow_two, ← mul_assoc, series_e, add_mul, mul_assoc (X ^ (r + 1)), series_a]
  have h := ident_a (X : PowerSeries ℤ) r
  rw [Dser]
  linear_combination X * h

/-- `M₂(r, n) = Tr (adjMat r n)²`. -/
noncomputable def M2 (r n : ℕ) : ℤ := Matrix.trace (adjMat r n ^ 2)

/-- **Second moment, all ranges `r`**:
`(∑ₙ Tr (A_{n,r})² zⁿ) · (1 − z − z^{r+1})² = 2z` (formal power series over `ℤ`). -/
theorem second_moment_series (r : ℕ) :
    PowerSeries.mk (fun n => M2 r n) * (1 - X - X ^ (r + 1)) ^ 2 = 2 * X := by
  have : PowerSeries.mk (fun n => M2 r n) = 2 * PowerSeries.mk (fun n => (e r n : ℤ)) := by
    ext n; simp [M2, trace_sq_eq]
  rw [this, mul_assoc, ← Dser, series_e_sq]

/-- Coefficient form: `[zⁿ] ((∑ₖ Tr A_{k,r}² zᵏ) · D_r²) = 2·[n = 1]`. -/
theorem second_moment_coeff (r n : ℕ) :
    coeff n (PowerSeries.mk (fun n => M2 r n) * (1 - X - X ^ (r + 1)) ^ 2) =
      if n = 1 then 2 else 0 := by
  rw [second_moment_series, coeff_ofNat_mul, coeff_X]
  split_ifs <;> simp

end Series

/-! ### Statements (not proved here) -/

section Statements

open PowerSeries

/-- `M k r n = Tr (adjMat r n)^k`. -/
noncomputable def Mk (k r n : ℕ) : ℤ := Matrix.trace (adjMat r n ^ k)

/-- **Fourth-moment statement (unproved; checked numerically for `r = 1..4`, `n ≤ 13`).**
`(∑ₙ Tr A_{n,r}⁴ zⁿ) · D_r³ = 2z·D_r + 4z²(1 + … + z^{r−1})·D_r + 24 z^{r+2}`. -/
def Conj4 (r : ℕ) : Prop :=
  PowerSeries.mk (fun n => Mk 4 r n) * (1 - X - X ^ (r + 1)) ^ 3 =
    2 * X * (1 - X - X ^ (r + 1)) +
      4 * X ^ 2 * (∑ g ∈ range r, X ^ g) * (1 - X - X ^ (r + 1)) + 24 * X ^ (r + 2)

/-- **General conjecture (unproved; evidence: `Certificates/blockade_verify.py`, `r = 1..4`,
finite windows).**  For `m ≥ 1`, `r ≥ 1` there is `P ∈ ℤ[z]` with
`(∑ₙ Tr A_{n,r}^{2m} zⁿ) · D_r^{m+1} = P`, `deg P = (2r+1)(m−1)+1`, and
`P ≡ (2m)! · z^{(r+1)m−r} (mod D_r)`.  For `r = 1` the first two parts are
`APEX.PXP.pxp_moment_rational` / `pxp_numerator_natDegree` and the last is `pxp_moment_residue`.

What has to change in the PXP proof (`Rational`/`Degree`/`Residue`, predicates
`Good`/`GoodT`/`GoodR`):
* Spatial compatibility.  `Compat β γ` (no common occupied time) must hold for every pair of
  trajectories at distance `≤ r`, not only for nearest neighbours.  The transfer recursion `g`
  must therefore carry the last `r` trajectories `(β_{j−r+1}, …, β_j)` as its state (instead of
  `β_j` alone), together with the used flip set `F`; `card_walks_eq_card_arrays` generalises
  verbatim (a closed walk is still an array of trajectories with pairwise disjoint flip sets
  covering all times, `PD`/`U`), with `CC` replaced by the range-`r` blockade.
* Inactive runs.  Constant trajectories (`zero`/`one`) between active sites form range-`r`
  admissible words.  A `one` site cannot lie within distance `r` of an active site
  (`not_compat_one_of_nonempty`), so an inactive run at the boundary contributes `1/D_r`
  (identity `ident_a`: `S_r + z^r B_r/D_r = 1/D_r`), and an internal run of length `g`
  between two active sites contributes `S_r + z^r/D_r` (identity `ident_b`), where the
  polynomial part `S_r = 1 + … + z^{r−1}` collects the short all-`zero` gaps in which the two
  active sites still interact through the blockade.  In PXP (`r = 1`) this is `1 + z/D`.
* Degree bookkeeping.  `Good S e d` must be re-based on `D_r` (degree `r+1`, leading
  coefficient `−1`, constant `1`); the lifting lemma `GoodT.lift` becomes
  `GoodT S e d c → GoodT S (e+1) (d+r+1) (−c)` and the "new active site after a long gap" step
  adds `z^r/D_r` (degree increment `2r+1` per further active site, giving `(2r+1)(m−1)+1`).
  Clusters of active sites at mutual distance `≤ r` replace the PXP pattern
  "consecutive active sites separated" and must be enumerated with the range-`r` `Compat`.
* Residue.  Modulo `D_r` only the arrays where every active site flips exactly twice and all
  active sites are pairwise at distance `> r` survive (the `z^r/D_r` gap is `≡ 0` after
  multiplying by `D_r`, the boundary factors give `1`); they are counted by `(2m)!` and occupy
  `m + r(m−1)` sites, whence `(2m)!·z^{(r+1)m−r}`.  The `Special`/`pulse` construction of
  `Degree.lean` must be redone with pulses at distance `r+1`. -/
def ConjGeneral : Prop :=
  ∀ m r : ℕ, 1 ≤ m → 1 ≤ r → ∃ P : Polynomial ℤ,
    P.natDegree = (2 * r + 1) * (m - 1) + 1 ∧
    PowerSeries.mk (fun n => Mk (2 * m) r n) * (1 - X - X ^ (r + 1)) ^ (m + 1) =
      (P : PowerSeries ℤ) ∧
    (1 - Polynomial.X - Polynomial.X ^ (r + 1) : Polynomial ℤ) ∣
      P - Polynomial.C ((Nat.factorial (2 * m) : ℕ) : ℤ) * Polynomial.X ^ ((r + 1) * m - r)

/-- Sanity link: the `k = 2` case of `Mk` is `M2`. -/
theorem Mk_two (r n : ℕ) : Mk 2 r n = M2 r n := rfl

end Statements

end APEX.Blockade

