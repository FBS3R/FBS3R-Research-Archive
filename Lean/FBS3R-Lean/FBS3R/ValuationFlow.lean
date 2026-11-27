/-
# Dilation flow of positive valuation mixtures (2026-08-09, 2026-08-10, 2026-08-11)

For a finite mixture `ε(A) = Σ_s C_s A^s` (real exponents, `A > 0`) put
`D = A d/dA`, `m₁ = Dε/ε = Σ s C_s A^s / ε`, `m₂ = Σ s² C_s A^s / ε` and the equation of
state `w = −1 − m₁/3`.

Machine-checked here:
* `mixture_flow` : `D w = −(m₂ − m₁²)/3` (exact derivative, any real exponents);
* `mixture_variance_nonneg` : for `C_s ≥ 0`, `m₂ − m₁² ≥ 0`, hence `D w ≤ 0`
  ("positive-mixture monotonicity test", 2026-08-10/11; log-convexity, 2026-08-09);
* `lambda_X_flow` : for the two-branch spectrum `{0, −1}` (`m₁ = −r`, `m₂ = r`, `0 ≤ r ≤ 1`):
  `D w = (1 + w)(2 + 3w)` and `−1 ≤ w ≤ −2/3` ("exact positive Λ+X flow");
* `cpl_tangent` : `w₀ = −1 + r/3`, `w_a = −D w|_{a=1} = r(1 − r)/3` ("local CPL tangent").
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace FBS3R.Valuation

open Real Finset

variable {ι : Type*} (s : Finset ι) (C e : ι → ℝ)

/-- The mixture density. -/
noncomputable def ε (a : ℝ) : ℝ := ∑ i ∈ s, C i * a ^ e i
/-- First dilation numerator `Dε = Σ s C_s A^s`. -/
noncomputable def N1 (a : ℝ) : ℝ := ∑ i ∈ s, e i * C i * a ^ e i
/-- Second dilation numerator `D²ε = Σ s² C_s A^s`. -/
noncomputable def N2 (a : ℝ) : ℝ := ∑ i ∈ s, e i ^ 2 * C i * a ^ e i
/-- Equation of state `w = −1 − (Dε/ε)/3`. -/
noncomputable def w (a : ℝ) : ℝ := -1 - N1 s C e a / (3 * ε s C e a)

theorem hasDerivAt_ε (a : ℝ) (ha : 0 < a) :
    HasDerivAt (ε s C e) (N1 s C e a / a) a := by
  have h : ∀ i ∈ s, HasDerivAt (fun y => C i * y ^ e i) (C i * (e i * a ^ (e i - 1))) a :=
    fun i _ => (hasDerivAt_rpow_const (Or.inl ha.ne')).const_mul (C i)
  have := HasDerivAt.sum h
  convert this using 1
  · ext y; simp [ε]
  · simp only [N1, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [rpow_sub_one ha.ne']; field_simp

theorem hasDerivAt_N1 (a : ℝ) (ha : 0 < a) :
    HasDerivAt (N1 s C e) (N2 s C e a / a) a := by
  have h : ∀ i ∈ s, HasDerivAt (fun y => e i * C i * y ^ e i)
      (e i * C i * (e i * a ^ (e i - 1))) a :=
    fun i _ => (hasDerivAt_rpow_const (Or.inl ha.ne')).const_mul (e i * C i)
  have := HasDerivAt.sum h
  convert this using 1
  · ext y; simp [N1]
  · simp only [N2, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [rpow_sub_one ha.ne']; field_simp

/-- **Exact dilation flow of the equation of state**: `A·w'(A) = −(m₂ − m₁²)/3`. -/
theorem mixture_flow (a : ℝ) (ha : 0 < a) (hε : 0 < ε s C e a) :
    ∃ w', HasDerivAt (w s C e) w' a ∧
      a * w' = -((N2 s C e a / ε s C e a) - (N1 s C e a / ε s C e a) ^ 2) / 3 := by
  have h1 := hasDerivAt_N1 s C e a ha
  have h2 := (hasDerivAt_ε s C e a ha).const_mul 3
  have h3 := (h1.div h2 (by positivity)).const_sub (-1)
  refine ⟨_, h3, ?_⟩
  field_simp

/-- For nonnegative coefficients the dilation variance is nonnegative, so `D w ≤ 0`. -/
theorem mixture_variance_nonneg (a : ℝ) (ha : 0 < a) (hC : ∀ i ∈ s, 0 ≤ C i)
    (hε : 0 < ε s C e a) :
    0 ≤ (N2 s C e a / ε s C e a) - (N1 s C e a / ε s C e a) ^ 2 := by
  have hcs : N1 s C e a ^ 2 ≤ ε s C e a * N2 s C e a := by
    unfold N1 ε N2
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i hi; exact mul_nonneg (hC i hi) (rpow_nonneg ha.le _)
    · intro i hi; exact mul_nonneg (mul_nonneg (sq_nonneg _) (hC i hi)) (rpow_nonneg ha.le _)
    · intro i _; apply le_of_eq; ring
  rw [div_pow, sub_nonneg, div_le_div_iff₀ (by positivity) hε]
  nlinarith

/-- **Exact positive Λ+X flow**: two branches `{0, −1}` give `m₁ = −r`, `m₂ = r`; then
`D w = (1 + w)(2 + 3w)` with `−1 ≤ w ≤ −2/3`. -/
theorem lambda_X_flow (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    let m1 := -r; let m2 := r; let ww := -1 - m1 / 3
    (1 + ww) * (2 + 3 * ww) = -(m2 - m1 ^ 2) / 3 ∧ -1 ≤ ww ∧ ww ≤ -2 / 3 := by
  intro m1 m2 ww
  refine ⟨by simp only [m1, m2, ww]; ring, by simp only [ww, m1]; linarith,
    by simp only [ww, m1]; linarith⟩

/-- Two-branch moments: for `ε = C₀ + C₁ A^{−1}` one has `m₁ = −r`, `m₂ = r` with
`r = C₁A^{−1}/ε`. -/
theorem two_branch_moments (C0 C1 a : ℝ) (hε : C0 + C1 * a ^ (-1 : ℝ) ≠ 0) :
    (0 * C0 * a ^ (0 : ℝ) + (-1) * C1 * a ^ (-1 : ℝ)) / (C0 * a ^ (0 : ℝ) + C1 * a ^ (-1 : ℝ))
        = -(C1 * a ^ (-1 : ℝ) / (C0 + C1 * a ^ (-1 : ℝ))) ∧
      (0 ^ 2 * C0 * a ^ (0 : ℝ) + (-1) ^ 2 * C1 * a ^ (-1 : ℝ))
          / (C0 * a ^ (0 : ℝ) + C1 * a ^ (-1 : ℝ))
        = C1 * a ^ (-1 : ℝ) / (C0 + C1 * a ^ (-1 : ℝ)) := by
  simp only [rpow_zero, mul_one]
  constructor
  · rw [← neg_div]; congr 1; ring
  · congr 1; ring

/-- **Local CPL tangent** of the positive Λ+X branch. -/
theorem cpl_tangent (r : ℝ) :
    let w0 := -1 + r / 3; let Dw := -(r - r ^ 2) / 3
    w0 = -1 - (-r) / 3 ∧ -Dw = r * (1 - r) / 3 := by
  intro w0 Dw; constructor <;> simp only [w0, Dw] <;> ring

end FBS3R.Valuation
