import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Collatz: no bounded additive correction makes `log` a Lyapunov function

`T n = (3n+1) / 2^{ν₂(3n+1)}` (the accelerated odd Collatz map).
Mersenne orbit: `T^[j] (2^(L+1) - 1) = 3^j * 2^(L+1-j) - 1` for `j ≤ L`.
Consequence: there is no bounded `b : ℕ → ℝ` with `log (T n) + b (T n) ≤ log n + b n` for every odd `n`.
-/

namespace APEX.Collatz

/-- Odd part of a natural number (`oddPart 0 = 0`): divide by 2 while possible. -/
def oddPart (m : ℕ) : ℕ :=
  if h : m ≠ 0 ∧ 2 ∣ m then oddPart (m / 2) else m
decreasing_by omega

/-- Accelerated (Syracuse) Collatz map `T n = (3n+1) / 2^{ν₂(3n+1)}`. -/
def T (n : ℕ) : ℕ := oddPart (3 * n + 1)

lemma oddPart_of_odd {m : ℕ} (hm : ¬ 2 ∣ m) : oddPart m = m := by
  rw [oddPart]; simp [hm]

lemma oddPart_two_mul {m : ℕ} (hm0 : m ≠ 0) : oddPart (2 * m) = oddPart m := by
  rw [oddPart, dif_pos ⟨by omega, dvd_mul_right 2 m⟩, Nat.mul_div_cancel_left _ (by norm_num)]

lemma oddPart_two_pow_mul (k m : ℕ) (hm : ¬ 2 ∣ m) : oddPart (2 ^ k * m) = m := by
  induction k with
  | zero => simpa using oddPart_of_odd hm
  | succ k ih =>
    have : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
    rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc, oddPart_two_mul (by positivity), ih]

/-- `T` agrees with the `2`-adic normal form: `T n = m` whenever `3n+1 = 2^k m` with `m` odd. -/
lemma T_eq_of_decomp {n k m : ℕ} (h : 3 * n + 1 = 2 ^ k * m) (hm : ¬ 2 ∣ m) : T n = m := by
  unfold T; rw [h, oddPart_two_pow_mul k m hm]

/-- One step on `2X - 1` with `X` even and positive. -/
lemma T_two_mul_sub_one {X : ℕ} (hX : 2 ∣ X) (hX0 : 0 < X) : T (2 * X - 1) = 3 * X - 1 := by
  have h1 : 3 * (2 * X - 1) + 1 = 2 * (3 * X - 1) := by omega
  have hodd : ¬ 2 ∣ 3 * X - 1 := by omega
  have hne : 3 * X - 1 ≠ 0 := by omega
  exact T_eq_of_decomp (k := 1) (by rw [h1, pow_one]) hodd

/-- The Mersenne orbit. -/
theorem T_iter_mersenne (L j : ℕ) (hj : j ≤ L) :
    T^[j] (2 ^ (L + 1) - 1) = 3 ^ j * 2 ^ (L + 1 - j) - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hX : 2 ∣ 3 ^ j * 2 ^ (L - j) := by
      apply Dvd.dvd.mul_left
      exact dvd_pow_self 2 (by omega)
    have hX0 : 0 < 3 ^ j * 2 ^ (L - j) := by positivity
    have e1 : 3 ^ j * 2 ^ (L + 1 - j) = 2 * (3 ^ j * 2 ^ (L - j)) := by
      rw [show L + 1 - j = (L - j) + 1 by omega, pow_succ]; ring
    have e2 : 3 ^ (j + 1) * 2 ^ (L + 1 - (j + 1)) = 3 * (3 ^ j * 2 ^ (L - j)) := by
      rw [show L + 1 - (j + 1) = L - j by omega, pow_succ]; ring
    rw [e1, e2, T_two_mul_sub_one hX hX0]

lemma mersenne_odd (L j : ℕ) (hj : j ≤ L) : Odd (3 ^ j * 2 ^ (L + 1 - j) - 1) := by
  have hX0 : 0 < 3 ^ j * 2 ^ (L - j) := by positivity
  have e1 : 3 ^ j * 2 ^ (L + 1 - j) = 2 * (3 ^ j * 2 ^ (L - j)) := by
    rw [show L + 1 - j = (L - j) + 1 by omega, pow_succ]; ring
  rw [e1]
  exact ⟨3 ^ j * 2 ^ (L - j) - 1, by omega⟩

/-- Height gain along the Mersenne orbit: `T^[L] (2^(L+1)-1) = 2·3^L - 1`. -/
theorem T_iter_mersenne_end (L : ℕ) : T^[L] (2 ^ (L + 1) - 1) = 2 * 3 ^ L - 1 := by
  rw [T_iter_mersenne L L le_rfl, show L + 1 - L = 1 by omega, pow_one, mul_comm]

/-- **Bounded-correction impossibility.** No bounded `b` turns `log` into a quantity that is
non-increasing along every odd step of `T`. -/
theorem no_bounded_log_correction :
    ¬ ∃ (b : ℕ → ℝ) (B : ℝ), (∀ n, |b n| ≤ B) ∧
      ∀ n, Odd n → Real.log (T n) + b (T n) ≤ Real.log n + b n := by
  rintro ⟨b, B, hB, hdec⟩
  -- telescoping along the Mersenne orbit
  have tele : ∀ L j, j ≤ L →
      Real.log (T^[j] (2 ^ (L + 1) - 1) : ℕ) + b (T^[j] (2 ^ (L + 1) - 1)) ≤
        Real.log ((2 ^ (L + 1) - 1 : ℕ) : ℝ) + b (2 ^ (L + 1) - 1) := by
    intro L j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hodd : Odd (T^[j] (2 ^ (L + 1) - 1)) := by
        rw [T_iter_mersenne L j (by omega)]; exact mersenne_odd L j (by omega)
      rw [Function.iterate_succ_apply']
      exact (hdec _ hodd).trans (ih (by omega))
  have key : ∀ L : ℕ, (L : ℝ) * Real.log (3 / 2) ≤ 2 * B + Real.log 2 := by
    intro L
    have h := tele L L le_rfl
    rw [T_iter_mersenne_end] at h
    have hb1 := abs_le.mp (hB (2 * 3 ^ L - 1))
    have hb2 := abs_le.mp (hB (2 ^ (L + 1) - 1))
    -- lower bound for the endpoint, upper bound for the start
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

/-- `log_φ 3 ∈ (2,3)`: `φ² < 3 < φ³`. -/
theorem goldenRatio_sq_lt_three_lt_cube :
    Real.goldenRatio ^ 2 < 3 ∧ 3 < Real.goldenRatio ^ 3 := by
  have h2 : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hlt : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hgt : 1 < Real.goldenRatio := Real.one_lt_goldenRatio
  refine ⟨by rw [h2]; linarith, ?_⟩
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    rw [pow_succ, h2]; nlinarith [h2]
  rw [h3]; linarith

end APEX.Collatz
