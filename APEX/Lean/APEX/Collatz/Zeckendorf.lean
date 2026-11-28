import APEX.Collatz.BoundedCorrection
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Collatz and the Fibonacci (Zeckendorf) height

For `n ≥ 1` the *Fibonacci height* `fibHeight n` is the unique `k ≥ 2` with
`fib k ≤ n < fib (k+1)` (defined as the least `k` with `n < fib (k+1)`).

Proved:
* `fibHeight_spec`, `two_le_fibHeight`, `fibHeight_eq_of`: characterization and uniqueness.
* `no_bounded_height_correction`: there is no bounded `b : ℕ → ℤ` such that
  `fibHeight (T n) + b (T n) ≤ fibHeight n + b n` for every odd `n > 1`
  (`T` the Syracuse map of `APEX.Collatz.BoundedCorrection`).
* `no_bounded_log_correction_gt_one`: the `log` version, quantified only over odd `n > 1`.
* `fibHeight_three_mul_add_one`: for `n ≥ 1`, `h n + 2 ≤ h (3n+1) ≤ h n + 3`.
* `fibHeight_gain_three_iff`: for `n ≥ 1`, `h (3n+1) = h n + 3 ↔ fib (h n + 3) ≤ 3n+1`.
* `card_gain_three`: for `k ≥ 2`, the number of `n ∈ [fib k, fib (k+1))` with gain `3`
  is `(fib (k+1) - fib k + 1) / 3` (floor division).
-/

namespace APEX.Collatz

open Nat

lemma exists_lt_fib_succ (n : ℕ) : ∃ k, n < fib (k + 1) :=
  ⟨n + 1, by show n < fib (n + 2); have := Nat.le_fib_add_one (n + 2); omega⟩

/-- Fibonacci height: the least `k` with `n < fib (k+1)`. For `n ≥ 1` it is the unique `k ≥ 2`
with `fib k ≤ n < fib (k+1)`. -/
def fibHeight (n : ℕ) : ℕ := Nat.find (exists_lt_fib_succ n)

lemma lt_fib_fibHeight_succ (n : ℕ) : n < fib (fibHeight n + 1) :=
  Nat.find_spec (exists_lt_fib_succ n)

lemma fib_fibHeight_le (n : ℕ) : fib (fibHeight n) ≤ n := by
  rcases h : fibHeight n with _ | j
  · simp
  · have hj : j < fibHeight n := by omega
    have := Nat.find_min (exists_lt_fib_succ n) hj
    omega

theorem fibHeight_spec (n : ℕ) : fib (fibHeight n) ≤ n ∧ n < fib (fibHeight n + 1) :=
  ⟨fib_fibHeight_le n, lt_fib_fibHeight_succ n⟩

/-- Uniqueness: any `k` with `fib k ≤ n < fib (k+1)` is the height. -/
theorem fibHeight_eq_of {n k : ℕ} (h1 : fib k ≤ n) (h2 : n < fib (k + 1)) : fibHeight n = k := by
  have hle : fibHeight n ≤ k := Nat.find_le h2
  apply le_antisymm hle
  by_contra hlt
  push Not at hlt
  have := Nat.fib_mono (show fibHeight n + 1 ≤ k by omega)
  have := lt_fib_fibHeight_succ n
  omega

theorem two_le_fibHeight {n : ℕ} (hn : 1 ≤ n) : 2 ≤ fibHeight n := by
  have := lt_fib_fibHeight_succ n
  rcases h : fibHeight n with _ | _ | j
  · rw [h] at this; simp at this; omega
  · rw [h] at this; simp at this; omega
  · omega

lemma fib_succ_le_two_mul {k : ℕ} (hk : 1 ≤ k) : fib (k + 1) ≤ 2 * fib k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show j + 1 + 1 = j + 2 by omega, Nat.fib_add_two]
  have := @Nat.fib_le_fib_succ j
  omega

lemma fib_add_le_two_pow_mul {k : ℕ} (hk : 1 ≤ k) (m : ℕ) : fib (k + m) ≤ 2 ^ m * fib k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have := fib_succ_le_two_mul (k := k + m) (by omega)
    rw [← add_assoc, pow_succ]
    nlinarith

lemma two_pow_mul_le_three_pow (L : ℕ) : 2 ^ L * (L + 2) ≤ 2 * 3 ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have : 2 ^ L ≤ 3 ^ L := Nat.pow_le_pow_left (by norm_num) L
    rw [pow_succ, pow_succ]
    nlinarith

lemma mersenne_gt_one (L j : ℕ) (hj : j < L) : 1 < 3 ^ j * 2 ^ (L + 1 - j) - 1 := by
  have h3 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 4 ≤ 2 ^ (L + 1 - j) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (L + 1 - j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 4 ≤ 3 ^ j * 2 ^ (L + 1 - j) := by nlinarith
  omega

/-- Telescoping along the Mersenne orbit, for any function `V` that is non-increasing along
odd steps from `n > 1`. -/
lemma mersenne_tele {α : Type*} [Preorder α] (V : ℕ → α)
    (hdec : ∀ n, Odd n → 1 < n → V (T n) ≤ V n) (L j : ℕ) (hj : j ≤ L) :
    V (T^[j] (2 ^ (L + 1) - 1)) ≤ V (2 ^ (L + 1) - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hodd : Odd (T^[j] (2 ^ (L + 1) - 1)) := by
      rw [T_iter_mersenne L j (by omega)]; exact mersenne_odd L j (by omega)
    have hgt : 1 < T^[j] (2 ^ (L + 1) - 1) := by
      rw [T_iter_mersenne L j (by omega)]; exact mersenne_gt_one L j (by omega)
    rw [Function.iterate_succ_apply']
    exact (hdec _ hodd hgt).trans (ih (by omega))

/-- **No bounded correction of the Fibonacci height.** -/
theorem no_bounded_height_correction :
    ¬ ∃ (b : ℕ → ℤ) (B : ℕ), (∀ n, |b n| ≤ B) ∧
      ∀ n, Odd n → 1 < n → (fibHeight (T n) : ℤ) + b (T n) ≤ fibHeight n + b n := by
  rintro ⟨b, B, hB, hdec⟩
  set C := 2 ^ (2 * B + 1) with hC
  set L := 4 * C
  have tele := mersenne_tele (fun n => (fibHeight n : ℤ) + b n) hdec L L le_rfl
  rw [T_iter_mersenne_end] at tele
  set x := 2 ^ (L + 1) - 1 with hx
  set y := 2 * 3 ^ L - 1 with hy
  have hb1 := abs_le.mp (hB y)
  have hb2 := abs_le.mp (hB x)
  have hhy : fibHeight y ≤ fibHeight x + 2 * B := by omega
  have hx1 : 1 ≤ x := by
    have := Nat.one_lt_two_pow (n := L + 1) (by omega); omega
  have hk := two_le_fibHeight hx1
  have e1 : y < fib (fibHeight y + 1) := lt_fib_fibHeight_succ y
  have e2 : fib (fibHeight y + 1) ≤ fib (fibHeight x + (2 * B + 1)) :=
    Nat.fib_mono (by omega)
  have e3 := fib_add_le_two_pow_mul (k := fibHeight x) (by omega) (2 * B + 1)
  rw [← hC] at e3
  have e4 := fib_fibHeight_le x
  have hyx : y < C * x := by
    have : C * fib (fibHeight x) ≤ C * x := Nat.mul_le_mul_left _ e4
    omega
  -- but `C * 2^(L+1) ≤ 3^L`
  have hgrow := two_pow_mul_le_three_pow L
  have hCpos : 0 < C := by positivity
  have hpow : 0 < 2 ^ L := by positivity
  have h3 : C * 2 ^ (L + 1) ≤ 3 ^ L := by
    rw [pow_succ]
    have : 2 ^ L * (L + 2) ≥ 2 ^ L * (4 * C) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hxlt : x < 2 ^ (L + 1) := by omega
  have : C * x < C * 2 ^ (L + 1) := Nat.mul_lt_mul_of_pos_left hxlt hCpos
  have h31 : 1 ≤ 3 ^ L := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- The `log` version of the bounded-correction impossibility, assuming the monotonicity only
for odd `n > 1`. -/
theorem no_bounded_log_correction_gt_one :
    ¬ ∃ (b : ℕ → ℝ) (B : ℝ), (∀ n, |b n| ≤ B) ∧
      ∀ n, Odd n → 1 < n → Real.log (T n) + b (T n) ≤ Real.log n + b n := by
  rintro ⟨b, B, hB, hdec⟩
  have key : ∀ L : ℕ, (L : ℝ) * Real.log (3 / 2) ≤ 2 * B + Real.log 2 := by
    intro L
    have h := mersenne_tele (fun n => Real.log (n : ℝ) + b n) hdec L L le_rfl
    rw [T_iter_mersenne_end] at h
    have hb1 := abs_le.mp (hB (2 * 3 ^ L - 1))
    have hb2 := abs_le.mp (hB (2 ^ (L + 1) - 1))
    have hlo : (3 : ℝ) ^ L ≤ ((2 * 3 ^ L - 1 : ℕ) : ℝ) := by
      have : 3 ^ L ≤ 2 * 3 ^ L - 1 := by have := Nat.one_le_pow L 3 (by norm_num); omega
      exact_mod_cast this
    have hhi : ((2 ^ (L + 1) - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
      have : 2 ^ (L + 1) - 1 ≤ 2 ^ (L + 1) := Nat.sub_le _ _
      exact_mod_cast this
    have hpos0 : (0 : ℝ) < ((2 ^ (L + 1) - 1 : ℕ) : ℝ) := by
      have : 1 ≤ 2 ^ (L + 1) - 1 := by
        have := Nat.one_lt_two_pow (n := L + 1) (by omega); omega
      exact_mod_cast this
    have l1 : Real.log ((3 : ℝ) ^ L) ≤ Real.log ((2 * 3 ^ L - 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hlo
    have l2 : Real.log ((2 ^ (L + 1) - 1 : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (L + 1)) :=
      Real.log_le_log hpos0 hhi
    rw [Real.log_pow] at l1
    rw [Real.log_pow] at l2
    rw [Real.log_div (by norm_num) (by norm_num)]
    push_cast at l2
    nlinarith
  have hl : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  obtain ⟨L, hL⟩ := exists_nat_gt ((2 * B + Real.log 2) / Real.log (3 / 2))
  have := key L
  rw [div_lt_iff₀ hl] at hL
  linarith

/-- Basic bounds: with `k = h n`, `fib (k+2) ≤ 3n+1 < fib (k+4)`. -/
lemma three_mul_add_one_bounds {n : ℕ} (hn : 1 ≤ n) :
    fib (fibHeight n + 2) ≤ 3 * n + 1 ∧ 3 * n + 1 < fib (fibHeight n + 4) := by
  have hk := two_le_fibHeight hn
  have h1 := fib_fibHeight_le n
  have h2 := lt_fib_fibHeight_succ n
  have hs := fib_succ_le_two_mul (k := fibHeight n) (by omega)
  have a2 : fib (fibHeight n + 2) = fib (fibHeight n) + fib (fibHeight n + 1) := Nat.fib_add_two
  have a3 : fib (fibHeight n + 3) = fib (fibHeight n + 1) + fib (fibHeight n + 2) :=
    Nat.fib_add_two
  have a4 : fib (fibHeight n + 4) = fib (fibHeight n + 2) + fib (fibHeight n + 3) :=
    Nat.fib_add_two
  constructor <;> omega

/-- **Height gain of `n ↦ 3n+1` is 2 or 3.** -/
theorem fibHeight_three_mul_add_one {n : ℕ} (hn : 1 ≤ n) :
    fibHeight n + 2 ≤ fibHeight (3 * n + 1) ∧ fibHeight (3 * n + 1) ≤ fibHeight n + 3 := by
  obtain ⟨l, u⟩ := three_mul_add_one_bounds hn
  by_cases hc : 3 * n + 1 < fib (fibHeight n + 3)
  · rw [fibHeight_eq_of l hc]; omega
  · push Not at hc
    rw [fibHeight_eq_of hc u]; omega

/-- **Gain 3 criterion.** -/
theorem fibHeight_gain_three_iff {n : ℕ} (hn : 1 ≤ n) :
    fibHeight (3 * n + 1) = fibHeight n + 3 ↔ fib (fibHeight n + 3) ≤ 3 * n + 1 := by
  obtain ⟨l, u⟩ := three_mul_add_one_bounds hn
  by_cases hc : 3 * n + 1 < fib (fibHeight n + 3)
  · rw [fibHeight_eq_of l hc]; omega
  · push Not at hc
    rw [fibHeight_eq_of hc u]; simpa using hc

/-- **Count of gain-3 points in a Fibonacci block.** For `k ≥ 2`,
`#{n ∈ [F_k, F_{k+1}) : h(3n+1) = h n + 3} = ⌊(F_{k+1} - F_k + 1)/3⌋`. -/
theorem card_gain_three {k : ℕ} (hk : 2 ≤ k) :
    ((Finset.Ico (fib k) (fib (k + 1))).filter
        (fun n => fibHeight (3 * n + 1) = fibHeight n + 3)).card =
      (fib (k + 1) - fib k + 1) / 3 := by
  have a3 : fib (k + 3) = fib (k + 1) + fib (k + 2) := Nat.fib_add_two
  have a2 : fib (k + 2) = fib k + fib (k + 1) := Nat.fib_add_two
  have hm : fib k ≤ fib (k + 1) := Nat.fib_le_fib_succ
  have hpos : 0 < fib k := Nat.fib_pos.mpr (by omega)
  have hset : (Finset.Ico (fib k) (fib (k + 1))).filter
        (fun n => fibHeight (3 * n + 1) = fibHeight n + 3) =
      Finset.Ico ((fib (k + 3) + 1) / 3) (fib (k + 1)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, hg⟩
      have hh := fibHeight_eq_of h1 h2
      rw [fibHeight_gain_three_iff (by omega), hh] at hg
      omega
    · rintro ⟨h1, h2⟩
      have h1' : fib k ≤ n := by omega
      have hh := fibHeight_eq_of h1' h2
      refine ⟨⟨h1', h2⟩, ?_⟩
      rw [fibHeight_gain_three_iff (by omega), hh]
      omega
  rw [hset, Nat.card_Ico]
  omega

end APEX.Collatz

#print axioms APEX.Collatz.fibHeight_spec
#print axioms APEX.Collatz.fibHeight_eq_of
#print axioms APEX.Collatz.two_le_fibHeight
#print axioms APEX.Collatz.no_bounded_height_correction
#print axioms APEX.Collatz.no_bounded_log_correction_gt_one
#print axioms APEX.Collatz.fibHeight_three_mul_add_one
#print axioms APEX.Collatz.fibHeight_gain_three_iff
#print axioms APEX.Collatz.card_gain_three
