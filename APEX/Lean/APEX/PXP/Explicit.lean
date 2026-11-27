/-
# Explicit fourth and sixth moment generating functions (kernel-checked for all `n`)

From `pxp_moment_rational` the numerator `P_m` has degree `≤ 3m - 2`, so it is fixed by the
first `3m - 1` traces.  Those traces are evaluated by the Lean kernel (`decide +kernel`, which
is checked by the kernel itself — no `native_decide`).  This yields, for **every** chain length,

* `∑ₙ Tr Aₙ⁴ zⁿ = (2z + 2z² + 18z³ − 4z⁴) / (1 − z − z²)³`,
* `∑ₙ Tr Aₙ⁶ zⁿ = (2z + 8z² + 130z³ + 40z⁴ + 350z⁵ − 156z⁶ + 36z⁷) / (1 − z − z²)⁴`,

i.e. eqs. (4th) and (6th) of the 2026-10-23 preprint.
-/
import APEX.PXP.Main
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.ComputeDegree

namespace APEX.PXP

open PowerSeries

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- If a polynomial `Q` of degree `≤ 3m-2` matches the first `3m-1` coefficients of
`(∑ M zⁿ)·D^(m+1)`, then it is the numerator. -/
lemma numerator_eq (m : ℕ) (hm : 1 ≤ m) (Q : Polynomial ℤ) (hQ : Q.natDegree ≤ 3 * m - 2)
    (h : ∀ n ≤ 3 * m - 2,
      coeff n (PowerSeries.mk (fun n => M (2 * m) n) * (1 - X - X ^ 2) ^ (m + 1)) = Q.coeff n) :
    PowerSeries.mk (fun n => M (2 * m) n) * (1 - X - X ^ 2) ^ (m + 1) = (Q : PowerSeries ℤ) := by
  obtain ⟨P, hP, hPe⟩ := pxp_moment_rational m hm
  rw [hPe]
  congr 1
  ext n
  by_cases hn : n ≤ 3 * m - 2
  · rw [← h n hn, hPe, Polynomial.coeff_coe]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

lemma M4_vals : M 4 0 = 0 ∧ M 4 1 = 2 ∧ M 4 2 = 8 ∧ M 4 3 = 42 ∧ M 4 4 = 112 := by
  unfold M
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

lemma M6_vals : M 6 0 = 0 ∧ M 6 1 = 2 ∧ M 6 2 = 16 ∧ M 6 3 = 190 ∧ M 6 4 = 752 ∧
    M 6 5 = 2860 ∧ M 6 6 = 8356 ∧ M 6 7 = 22798 := by
  unfold M
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

lemma coeff_X_pow_mul_mk (f : ℕ → ℤ) (j n : ℕ) :
    coeff n (X ^ j * PowerSeries.mk f) = if j ≤ n then f (n - j) else 0 := by
  rw [PowerSeries.coeff_X_pow_mul', coeff_mk]

theorem fourth_moment_gf :
    PowerSeries.mk (fun n => M 4 n) * (1 - X - X ^ 2) ^ 3 =
      ((2 * Polynomial.X + 2 * Polynomial.X ^ 2 + 18 * Polynomial.X ^ 3 - 4 * Polynomial.X ^ 4 :
        Polynomial ℤ) : PowerSeries ℤ) := by
  have e := numerator_eq 2 (by norm_num)
    (2 * Polynomial.X + 2 * Polynomial.X ^ 2 + 18 * Polynomial.X ^ 3 - 4 * Polynomial.X ^ 4)
  simp only [show 2 * 2 = 4 by rfl, show 2 + 1 = 3 by rfl] at e
  apply e
  · compute_degree!
  · intro n hn
    have hD : PowerSeries.mk (fun n => M 4 n) * (1 - X - X ^ 2) ^ 3 =
        X ^ 0 * PowerSeries.mk (fun n => M 4 n) - 3 * (X ^ 1 * PowerSeries.mk (fun n => M 4 n))
        + 5 * (X ^ 3 * PowerSeries.mk (fun n => M 4 n))
        - 3 * (X ^ 5 * PowerSeries.mk (fun n => M 4 n))
        - X ^ 6 * PowerSeries.mk (fun n => M 4 n) := by ring
    obtain ⟨h0, h1, h2, h3, h4⟩ := M4_vals
    rw [hD]
    simp only [map_sub, map_add, coeff_X_pow_mul_mk]
    have c3 : ∀ S : PowerSeries ℤ, coeff n (3 * S) = 3 * coeff n S := fun S => by
      rw [show (3 : PowerSeries ℤ) = C (3 : ℤ) by rfl, coeff_C_mul]
    have c5 : ∀ S : PowerSeries ℤ, coeff n (5 * S) = 5 * coeff n S := fun S => by
      rw [show (5 : PowerSeries ℤ) = C (5 : ℤ) by rfl, coeff_C_mul]
    rw [c3, c3, c5]
    simp only [coeff_X_pow_mul_mk]
    interval_cases n <;> simp [h0, h1, h2, h3, h4, Polynomial.coeff_X_pow, Polynomial.coeff_X]

lemma coeff_ofNat_mul (n c : ℕ) [c.AtLeastTwo] (S : PowerSeries ℤ) :
    coeff n ((OfNat.ofNat c : PowerSeries ℤ) * S) = (OfNat.ofNat c : ℤ) * coeff n S := by
  rw [← map_ofNat (C (R := ℤ)) c, coeff_C_mul]

theorem sixth_moment_gf :
    PowerSeries.mk (fun n => M 6 n) * (1 - X - X ^ 2) ^ 4 =
      ((2 * Polynomial.X + 8 * Polynomial.X ^ 2 + 130 * Polynomial.X ^ 3 + 40 * Polynomial.X ^ 4
        + 350 * Polynomial.X ^ 5 - 156 * Polynomial.X ^ 6 + 36 * Polynomial.X ^ 7 :
        Polynomial ℤ) : PowerSeries ℤ) := by
  have e := numerator_eq 3 (by norm_num)
    (2 * Polynomial.X + 8 * Polynomial.X ^ 2 + 130 * Polynomial.X ^ 3 + 40 * Polynomial.X ^ 4
        + 350 * Polynomial.X ^ 5 - 156 * Polynomial.X ^ 6 + 36 * Polynomial.X ^ 7)
  simp only [show 2 * 3 = 6 by rfl, show 3 + 1 = 4 by rfl] at e
  apply e
  · compute_degree!
  · intro n hn
    set S := PowerSeries.mk (fun n => M 6 n) with hS
    have hD : S * (1 - X - X ^ 2) ^ 4 =
        X ^ 0 * S - 4 * (X ^ 1 * S) + 2 * (X ^ 2 * S) + 8 * (X ^ 3 * S) - 5 * (X ^ 4 * S)
        - 8 * (X ^ 5 * S) + 2 * (X ^ 6 * S) + 4 * (X ^ 7 * S) + X ^ 8 * S := by ring
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := M6_vals
    rw [hD]
    simp only [map_sub, map_add, coeff_ofNat_mul, hS, coeff_X_pow_mul_mk]
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, coeff_X_pow_mul_mk, Polynomial.coeff_X_pow,
      Polynomial.coeff_X]

end APEX.PXP
