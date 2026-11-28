/-
# Causal–spectral carrier on round `S³`: exact identities

Source: *Causal–Spectral Distinguishability Selection on a Conditional Round S³ Carrier*
(2026-07-07).  Machine-checked:
* geodesic-ball volume `Vol(B_s) = ∫₀ˢ 4πR² sin²(ρ/R) dρ = 2πR³ (s/R − ½ sin(2s/R))`,
  and `Vol(B_{πR}) = 2π²R³`;
* causal fraction `Γ(τ) = (τ − ½ sin 2τ)/π`: `Γ' = (2/π) sin²τ ≥ 0`, `Γ(τ)+Γ(π−τ) = 1`,
  `Γ(π/2) = 1/2`;
* scalar capacity: `n(n+2) ≤ x² ↔ n+1 ≤ √(1+x²)` and `Σ_{n<M}(n+1)² = M(M+1)(2M+1)/6`;
* TT capacity `Σ_{k=2}^{M} 2(k−1)(k+3) = M(M−1)(2M+11)/3`;
* Dirac capacity `2 Σ_{n=0}^{M}(n+1)(n+2) = 2(M+1)(M+2)(M+3)/3`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace FBS3R.CausalSpectral

open Real intervalIntegral Finset

/-- Geodesic-ball volume on `S³(R)`. -/
theorem ball_volume {R : ℝ} (hR : R ≠ 0) (s : ℝ) :
    ∫ ρ in (0 : ℝ)..s, 4 * π * R ^ 2 * sin (ρ / R) ^ 2
      = 2 * π * R ^ 3 * (s / R - 1 / 2 * sin (2 * s / R)) := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun x => sin x ^ 2) hR, integral_sin_sq]
  simp only [zero_div, sin_zero, cos_zero, zero_mul, smul_eq_mul]
  rw [show 2 * s / R = 2 * (s / R) by ring, sin_two_mul]
  ring

theorem total_volume {R : ℝ} (hR : 0 < R) :
    2 * π * R ^ 3 * ((π * R) / R - 1 / 2 * sin (2 * (π * R) / R)) = 2 * π ^ 2 * R ^ 3 := by
  rw [show 2 * (π * R) / R = 2 * π by field_simp, show π * R / R = π by field_simp]
  simp [sin_two_pi]; ring

/-- Causal accessibility fraction. -/
noncomputable def Γ (τ : ℝ) : ℝ := (τ - 1 / 2 * sin (2 * τ)) / π

theorem hasDerivAt_Γ (τ : ℝ) : HasDerivAt Γ (2 / π * sin τ ^ 2) τ := by
  have h1 : HasDerivAt (fun t : ℝ => sin (2 * t)) (cos (2 * τ) * 2) τ := by
    simpa using ((hasDerivAt_id τ).const_mul 2).sin
  have h := ((hasDerivAt_id' τ).sub (h1.const_mul (1 / 2))).div_const π
  show HasDerivAt (fun t => (t - 1 / 2 * sin (2 * t)) / π) _ τ
  convert h using 1
  rw [show cos (2 * τ) = 1 - 2 * sin τ ^ 2 by rw [cos_two_mul, cos_sq']; ring]
  ring

theorem Γ_symm (τ : ℝ) : Γ τ + Γ (π - τ) = 1 := by
  unfold Γ
  rw [show 2 * (π - τ) = 2 * π - 2 * τ by ring, sin_two_pi_sub]
  field_simp; ring

theorem Γ_half : Γ (π / 2) = 1 / 2 := by
  unfold Γ; rw [show 2 * (π / 2) = π by ring, sin_pi]
  simp only [mul_zero, sub_zero]; field_simp

/-- Scalar cutoff equivalence: `n(n+2) ≤ x² ⇔ n + 1 ≤ √(1+x²)`. -/
theorem scalar_cutoff (n : ℕ) (x : ℝ) :
    (n : ℝ) * (n + 2) ≤ x ^ 2 ↔ (n : ℝ) + 1 ≤ √(1 + x ^ 2) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith

theorem scalar_count (M : ℕ) :
    (∑ n ∈ range M, ((n : ℚ) + 1) ^ 2) = (M : ℚ) * (M + 1) * (2 * M + 1) / 6 := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih]; push_cast; ring

theorem TT_count (M : ℕ) (hM : 2 ≤ M) :
    (∑ k ∈ Icc 2 M, 2 * ((k : ℚ) - 1) * (k + 3)) = (M : ℚ) * (M - 1) * (2 * M + 11) / 3 := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast; ring

theorem dirac_count (M : ℕ) :
    2 * (∑ n ∈ range (M + 1), ((n : ℚ) + 1) * (n + 2)) = 2 * ((M : ℚ) + 1) * (M + 2) * (M + 3) / 3 := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [sum_range_succ, mul_add, ih]; push_cast; ring

end FBS3R.CausalSpectral
