/-
# Planck-boundary geometry of compact S³ cosmology (2026-05-05)

Machine-checked here:
* `riemannZeta_neg_three` : `ζ(-3) = 1/120` (from Mathlib's Bernoulli formula).
* `casimir_constant` : for the conformal scalar on S³ (`ν_ℓ = ℓ+1`, degeneracy `(ℓ+1)²`,
  so `ζ_ω(s) = ζ(s-2)`), `C_ζ = ½ ζ_ω(-1) = ½ ζ(-3) = 1/240`.
* `casimir_density` : `(C/a)/(2π²a³) = C/(2π²a⁴)`; with `C = 1/240` this is `1/(480π²a⁴)`.
* `hasDerivAt_hubble` : `H = ȧ/a` has `Ḣ = ä/a - H²`; hence `kretschmann_forms` : the two
  forms `12[(ä/a)² + ((ȧ²+1)/a²)²] = 12[(Ḣ+H²)² + (H²+1/a²)²]` agree.
* `kretschmann_bound` : `|H| ≤ h`, `|Ḣ| ≤ g`, `a ≥ ℓ > 0` give
  `K ≤ 12[(g+h²)² + (h²+1/ℓ²)²]` (the paper's `K(t_P) ≤ C/ℓ_P⁴`, with explicit `C`).

Not formalised: the Riemann tensor of FLRW (the Kretschmann formula is taken as input), the
analytic continuation of the spectral sum itself (we use `ζ_ω(s) = ζ(s-2)` as stated), the
Wheeler–DeWitt self-adjointness and the Noether-II identities.
-/
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

namespace FBS3R.Planck

open Real

theorem riemannZeta_neg_three : riemannZeta (-3) = 1 / 120 := by
  have h := riemannZeta_neg_nat_eq_bernoulli' 3
  have hb : bernoulli' 4 = -1 / 30 := bernoulli'_four
  push_cast at h
  rw [h, hb]
  push_cast; norm_num

/-- Casimir constant of the conformally coupled scalar on S³. -/
theorem casimir_constant : (1 / 2 : ℂ) * riemannZeta ((-1 : ℂ) - 2) = 1 / 240 := by
  rw [show (-1 : ℂ) - 2 = -3 by norm_num, riemannZeta_neg_three]; norm_num

theorem casimir_density (C a : ℝ) (ha : 0 < a) :
    (C / a) / (2 * π ^ 2 * a ^ 3) = C / (2 * π ^ 2 * a ^ 4) := by
  have : π ≠ 0 := pi_ne_zero
  field_simp

theorem casimir_density_scalar (a : ℝ) (ha : 0 < a) :
    ((1 / 240 : ℝ) / a) / (2 * π ^ 2 * a ^ 3) = 1 / (480 * π ^ 2 * a ^ 4) := by
  rw [casimir_density _ _ ha]; have : π ≠ 0 := pi_ne_zero; field_simp; ring_nf

theorem hasDerivAt_hubble {a a' : ℝ → ℝ} {a'' t : ℝ} (h1 : HasDerivAt a (a' t) t)
    (h2 : HasDerivAt a' a'' t) (h0 : a t ≠ 0) :
    HasDerivAt (fun s => a' s / a s) (a'' / a t - (a' t / a t) ^ 2) t := by
  convert h2.div h1 h0 using 1
  field_simp

theorem kretschmann_forms (a a' a'' : ℝ) (h0 : a ≠ 0) :
    let H := a' / a
    let Hd := a'' / a - H ^ 2
    12 * ((a'' / a) ^ 2 + ((a' ^ 2 + 1) / a ^ 2) ^ 2)
      = 12 * ((Hd + H ^ 2) ^ 2 + (H ^ 2 + 1 / a ^ 2) ^ 2) := by
  intro H Hd
  simp only [H, Hd]; field_simp; ring

theorem kretschmann_bound (H Hd a h g ℓ : ℝ) (hH : |H| ≤ h) (hHd : |Hd| ≤ g)
    (hℓ : 0 < ℓ) (ha : ℓ ≤ a) :
    12 * ((Hd + H ^ 2) ^ 2 + (H ^ 2 + 1 / a ^ 2) ^ 2)
      ≤ 12 * ((g + h ^ 2) ^ 2 + (h ^ 2 + 1 / ℓ ^ 2) ^ 2) := by
  have hH2 : H ^ 2 ≤ h ^ 2 := by
    rw [← sq_abs H]; gcongr
  have h1 : |Hd + H ^ 2| ≤ g + h ^ 2 := by
    calc |Hd + H ^ 2| ≤ |Hd| + |H ^ 2| := abs_add_le _ _
      _ ≤ g + h ^ 2 := by rw [abs_of_nonneg (sq_nonneg H)]; linarith
  have h2 : 1 / a ^ 2 ≤ 1 / ℓ ^ 2 := by gcongr
  have h3 : (Hd + H ^ 2) ^ 2 ≤ (g + h ^ 2) ^ 2 := by
    rw [← sq_abs]; gcongr
  have h4 : (H ^ 2 + 1 / a ^ 2) ^ 2 ≤ (h ^ 2 + 1 / ℓ ^ 2) ^ 2 := by
    have : 0 ≤ H ^ 2 + 1 / a ^ 2 := by positivity
    gcongr
  linarith

end FBS3R.Planck
