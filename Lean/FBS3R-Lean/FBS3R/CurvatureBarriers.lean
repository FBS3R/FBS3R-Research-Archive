/-
# Supercritical curvature barriers for Ricci-type flows on S³ (2026-07-05)

Machine-checked here (pointwise integrands; the integral over `M` is not formalised):
* `scale_derivative` : `d/ds|₀ e^{3s} Φ(e^{-4s}K) = 3Φ(K) - 4KΦ'(K)` (Prop. "scale derivative").
* `power_threshold` : for `Φ = K^q`, `4KΦ' - 3Φ = (4q-3)K^q`, positive iff `q > 3/4`.
* `barrier_sign` : for `Φ = (K+δ)^q/(K_P-K)^p`,
  `4KΦ' - 3Φ = Φ (4qK/(K+δ) + 4pK/(K_P-K) - 3)` (Prop. "barrier sign").
* `ricci_lower_bound_sharp` : in dimension three `|Rm|² = 4|Ric|² - R²`; if this is `≤ K₀` then
  every Ricci eigenvalue is `≥ -√(K₀/2)`. **This is sharper than the paper's constant**
  `-(1/2 + 1/√3)√K₀` (`paper_constant_weaker`), and `√(1/2)` is optimal (`ricci_bound_attained`).

The identity `|Rm|² = 4|Ric|² - R²` (Weyl tensor vanishes in dimension 3) is used as input:
Mathlib has no Riemann tensor.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace FBS3R.Barriers

open Real

theorem scale_derivative (Φ : ℝ → ℝ) (Φ' K : ℝ) (hΦ : HasDerivAt Φ Φ' K) :
    HasDerivAt (fun s => exp (3 * s) * Φ (exp (-4 * s) * K)) (3 * Φ K - 4 * K * Φ') 0 := by
  have h1 : HasDerivAt (fun s : ℝ => exp (3 * s)) (exp (3 * 0) * 3) 0 :=
    ((hasDerivAt_id 0).const_mul 3 |>.exp).congr_deriv (by simp)
  have h2 : HasDerivAt (fun s : ℝ => exp (-4 * s) * K) (exp (-4 * 0) * (-4) * K) 0 :=
    (((hasDerivAt_id 0).const_mul (-4) |>.exp).congr_deriv (by simp)).mul_const K
  have h3 : HasDerivAt (fun s => Φ (exp (-4 * s) * K)) (Φ' * (exp (-4 * 0) * (-4) * K)) 0 := by
    have hK : exp (-4 * 0) * K = K := by simp
    exact (hΦ.comp_of_eq 0 h2 hK.symm) |>.congr_deriv (by ring)
  convert h1.mul h3 using 1
  simp; ring

theorem power_threshold (q K : ℝ) (hK : 0 < K) :
    4 * K * (q * K ^ (q - 1)) - 3 * K ^ q = (4 * q - 3) * K ^ q ∧
      (0 < 4 * K * (q * K ^ (q - 1)) - 3 * K ^ q ↔ 3 / 4 < q) := by
  have e : 4 * K * (q * K ^ (q - 1)) - 3 * K ^ q = (4 * q - 3) * K ^ q := by
    rw [rpow_sub_one hK.ne']; field_simp
  refine ⟨e, ?_⟩
  rw [e]
  have hp : 0 < K ^ q := rpow_pos_of_pos hK q
  constructor
  · intro h; have := (pos_iff_pos_of_mul_pos h).mpr hp; linarith
  · intro h; exact mul_pos (by linarith) hp

/-- The Planck-wall barrier density. -/
noncomputable def Φb (δ KP p q K : ℝ) : ℝ := (K + δ) ^ q / (KP - K) ^ p

theorem hasDerivAt_Φb (δ KP p q K : ℝ) (h1 : 0 < K + δ) (h2 : 0 < KP - K) :
    HasDerivAt (Φb δ KP p q)
      (Φb δ KP p q K * (q / (K + δ) + p / (KP - K))) K := by
  have hA : HasDerivAt (fun y => (y + δ) ^ q) (1 * q * (K + δ) ^ (q - 1)) K :=
    ((hasDerivAt_id K).add_const δ).rpow_const (Or.inl h1.ne')
  have hB : HasDerivAt (fun y => (KP - y) ^ p) ((-1) * p * (KP - K) ^ (p - 1)) K :=
    ((hasDerivAt_id K).const_sub KP).rpow_const (Or.inl h2.ne')
  have hBpos : 0 < (KP - K) ^ p := rpow_pos_of_pos h2 p
  show HasDerivAt (fun y => (y + δ) ^ q / (KP - y) ^ p) _ K
  convert hA.div hB hBpos.ne' using 1
  unfold Φb
  rw [rpow_sub_one h1.ne', rpow_sub_one h2.ne']
  field_simp; ring

theorem barrier_sign (δ KP p q K : ℝ) (h1 : 0 < K + δ) (h2 : 0 < KP - K) :
    4 * K * (Φb δ KP p q K * (q / (K + δ) + p / (KP - K))) - 3 * Φb δ KP p q K
      = Φb δ KP p q K * (4 * q * K / (K + δ) + 4 * p * K / (KP - K) - 3) := by
  field_simp

/-- Sum-of-squares form behind the sharp Ricci bound. -/
theorem rm_form_sos (r₁ r₂ r₃ : ℝ) :
    4 * (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2) - (r₁ + r₂ + r₃) ^ 2
      = 2 * r₁ ^ 2 + (r₁ - r₂ - r₃) ^ 2 + 2 * (r₂ - r₃) ^ 2 := by ring

theorem ricci_lower_bound_sharp (r₁ r₂ r₃ K₀ : ℝ)
    (hK : 4 * (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2) - (r₁ + r₂ + r₃) ^ 2 ≤ K₀) :
    -√(K₀ / 2) ≤ r₁ := by
  have h : r₁ ^ 2 ≤ K₀ / 2 := by
    rw [rm_form_sos] at hK; nlinarith [sq_nonneg (r₁ - r₂ - r₃), sq_nonneg (r₂ - r₃)]
  have := Real.abs_le_sqrt h
  linarith [neg_abs_le r₁]

theorem ricci_bound_attained (t : ℝ) (ht : 0 ≤ t) :
    let r₁ := -2 * t; let r₂ := -t; let r₃ := -t
    4 * (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2) - (r₁ + r₂ + r₃) ^ 2 = 8 * t ^ 2 ∧
      r₁ = -√(8 * t ^ 2 / 2) := by
  intro r₁ r₂ r₃
  refine ⟨by simp only [r₁, r₂, r₃]; ring, ?_⟩
  simp only [r₁]
  rw [show 8 * t ^ 2 / 2 = (2 * t) ^ 2 by ring, sqrt_sq (by linarith)]; ring

theorem paper_constant_weaker : √(1 / 2 : ℝ) < 1 / 2 + 1 / √3 := by
  have h3 : √3 < 2 := by
    rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h3p : 0 < √3 := by positivity
  have hb : 1 / 2 < 1 / √3 := by rw [div_lt_div_iff₀ (by norm_num) h3p]; linarith
  have hs : √(1 / 2 : ℝ) < 1 := by
    rw [show (1:ℝ) = √1 by simp]; exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end FBS3R.Barriers
