import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Int.Basic

/-!
# Range-`r` Rydberg blockade: dimension of the constrained space

`Adm r w`: in the binary word `w`, any two `1`s are more than `r` sites apart
(`r = 1` is the PXP / Fibonacci constraint).  With `a r n = #{w : |w| = n, Adm r w}`:

* `a r n = n + 1` for `n ≤ r`,
* `a r (n + r + 1) = a r (n + r) + a r n`  (so `∑ aₙ zⁿ = (1+z+…+z^r)/(1 − z − z^{r+1})`).
-/

namespace APEX.Blockade

open Finset

/-- Blockade admissibility. -/
def Adm (r : ℕ) : List Bool → Prop
  | [] => True
  | false :: l => Adm r l
  | true :: l => (∀ x ∈ l.take r, x = false) ∧ Adm r l

/-- Decidability of `Adm`. -/
def decAdm (r : ℕ) : (l : List Bool) → Decidable (Adm r l)
  | [] => isTrue trivial
  | false :: l => decAdm r l
  | true :: l => @instDecidableAnd _ _ (inferInstanceAs (Decidable (∀ x ∈ l.take r, x = false)))
      (decAdm r l)

instance (r : ℕ) : DecidablePred (Adm r) := decAdm r

/-- All words of length `n`. -/
def allL : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (allL n).map ⟨List.cons false, List.cons_injective⟩ ∪
      (allL n).map ⟨List.cons true, List.cons_injective⟩

lemma mem_allL {n : ℕ} {w : List Bool} : w ∈ allL n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [allL]
  | succ n ih =>
    cases w with
    | nil => simp [allL]
    | cons b w => cases b <;> simp [allL, ih]

/-- The constrained configuration space `C_{n,r}`. -/
def C (r n : ℕ) : Finset (List Bool) := (allL n).filter (Adm r)

/-- Its dimension. -/
def a (r n : ℕ) : ℕ := (C r n).card

lemma mem_C {r n : ℕ} {w : List Bool} : w ∈ C r n ↔ w.length = n ∧ Adm r w := by
  simp [C, mem_allL]

/-- Words starting with `r` zeros (or all zeros when shorter). -/
def Z (r : ℕ) (w : List Bool) : Prop := ∀ x ∈ w.take r, x = false

instance (r : ℕ) : DecidablePred (Z r) := fun w => by unfold Z; infer_instance

lemma card_succ (r n : ℕ) : a r (n + 1) = a r n + ((C r n).filter (Z r)).card := by
  have : C r (n + 1) = (C r n).map ⟨List.cons false, List.cons_injective⟩ ∪
      ((C r n).filter (Z r)).map ⟨List.cons true, List.cons_injective⟩ := by
    ext w
    cases w with
    | nil => simp [mem_C]
    | cons b w => cases b <;> simp [mem_C, Adm, Z] <;> tauto
  unfold a
  rw [this, card_union_of_disjoint, card_map, card_map]
  rw [disjoint_left]
  intro w h1 h2
  simp only [mem_map, Function.Embedding.coeFn_mk] at h1 h2
  obtain ⟨u, -, rfl⟩ := h1
  obtain ⟨v, -, hv⟩ := h2
  simp at hv

lemma adm_replicate_append (r k : ℕ) (l : List Bool) :
    Adm r (List.replicate k false ++ l) ↔ Adm r l := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, Adm, ih]

lemma Z_iff_of_le {r : ℕ} {w : List Bool} (h : r ≤ w.length) :
    Z r w ↔ ∃ l, w = List.replicate r false ++ l := by
  constructor
  · intro hz
    refine ⟨w.drop r, ?_⟩
    conv_lhs => rw [← List.take_append_drop r w]
    congr 1
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp [List.length_take, h], hz⟩
  · rintro ⟨l, rfl⟩ x hx
    rw [List.take_append_of_le_length (by simp)] at hx
    simp at hx
    exact (List.eq_of_mem_replicate (by simpa using hx))

lemma card_Z_of_le (r n : ℕ) : ((C r (n + r)).filter (Z r)).card = a r n := by
  unfold a
  symm
  apply card_bij (fun l _ => List.replicate r false ++ l)
  · intro l hl
    rw [mem_C] at hl
    rw [mem_filter, mem_C, Z_iff_of_le (by simp [hl.1])]
    exact ⟨⟨by simp [hl.1, Nat.add_comm], (adm_replicate_append r r l).mpr hl.2⟩, l, rfl⟩
  · intro l1 _ l2 _ h; exact List.append_cancel_left h
  · intro w hw
    rw [mem_filter, mem_C] at hw
    obtain ⟨⟨hlen, hadm⟩, hz⟩ := hw
    obtain ⟨l, rfl⟩ := (Z_iff_of_le (by omega)).mp hz
    refine ⟨l, ?_, rfl⟩
    rw [mem_C]
    exact ⟨by simp at hlen; omega, (adm_replicate_append r r l).mp hadm⟩

lemma card_Z_of_lt (r n : ℕ) (h : n < r) : ((C r n).filter (Z r)).card = 1 := by
  rw [card_eq_one]
  refine ⟨List.replicate n false, ?_⟩
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

theorem a_zero (r : ℕ) : a r 0 = 1 := by
  simp only [a, C, allL]; rw [filter_singleton, if_pos (show Adm r [] from trivial), card_singleton]

/-- `a r n = n + 1` for `n ≤ r`. -/
theorem a_of_le (r n : ℕ) (h : n ≤ r) : a r n = n + 1 := by
  induction n with
  | zero => exact a_zero r
  | succ n ih => rw [card_succ, ih (by omega), card_Z_of_lt r n (by omega)]

/-- **Blockade recurrence** `aₙ = aₙ₋₁ + aₙ₋ᵣ₋₁`. -/
theorem a_rec (r n : ℕ) : a r (n + r + 1) = a r (n + r) + a r n := by
  rw [card_succ, card_Z_of_le]

/-- Coefficient form of `(∑ aₙ zⁿ)(1 − z − z^{r+1}) = 1 + z + … + z^r`. -/
theorem gf_coeff (r n : ℕ) :
    (a r n : ℤ) - (if 1 ≤ n then (a r (n - 1) : ℤ) else 0)
      - (if r + 1 ≤ n then (a r (n - r - 1) : ℤ) else 0) = if n ≤ r then 1 else 0 := by
  rcases Nat.lt_or_ge r n with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + r + 1 := ⟨n - r - 1, by omega⟩
    have := a_rec r k
    rw [if_pos (show 1 ≤ k + r + 1 by omega), if_pos (show r + 1 ≤ k + r + 1 by omega),
      if_neg (show ¬ (k + r + 1 ≤ r) by omega),
      show k + r + 1 - 1 = k + r by omega, show k + r + 1 - r - 1 = k by omega, this]
    push_cast; ring
  · rw [if_neg (show ¬ (r + 1 ≤ n) by omega), if_pos h, a_of_le r n h]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_pos (show 1 ≤ n by omega), a_of_le r (n - 1) (by omega)]
      push_cast [Nat.cast_sub hn]; ring

/-- PXP check: `a 1 n = F_{n+2}`. -/
theorem a_one_eq_fib (n : ℕ) : a 1 n = Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [a_zero]; rfl
    | 1, _ => rw [a_of_le 1 1 le_rfl]; rfl
    | k + 2, ih =>
      have := a_rec 1 k
      rw [show k + 2 = k + 1 + 1 by rfl, this, ih (k + 1) (by omega), ih k (by omega),
        Nat.fib_add_two (n := k + 2)]
      ring

end APEX.Blockade
