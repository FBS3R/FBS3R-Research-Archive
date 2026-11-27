/-
# Sharp pointwise bounds for finite spectral sectors (scalar-kernel form)

Source: *Killing–Beltrami algebra …*, Thm `thm:homogeneousprojector` and
Cor. `cor:uncertainty`.  The geometric input of the paper is that for a `G`-invariant
`N`-dimensional sector with orthonormal basis `eᵢ` on a homogeneous space, the kernel
`Σᵢ eᵢ(x)²` is constant.  Given that, everything else is checked here:
* the constant equals `N / V` (integrate over a space of volume `V`);
* pointwise bound `w(x)² ≤ ‖a‖² · N/V` for `w = Σ aᵢ eᵢ`, with equality at `a = e(x₀)`;
* hence the sharp concentration inequality `‖w‖₂² / w(x)² ≥ V/N`.
(The paper's vector-bundle version has an extra fibre-rank factor `r`.)
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace FBS3R.Projector

open MeasureTheory Finset

variable {X : Type*} [MeasurableSpace X] {N : ℕ}

/-- Constant kernel value equals `N / V`. -/
theorem kernel_const (μ : Measure X) (e : Fin N → X → ℝ) (K : ℝ)
    (hint : ∀ i, Integrable (fun x => e i x ^ 2) μ) (hnorm : ∀ i, ∫ x, e i x ^ 2 ∂μ = 1)
    (hK : ∀ x, ∑ i, e i x ^ 2 = K) : K * μ.real Set.univ = N := by
  have : ∫ x, (∑ i, e i x ^ 2) ∂μ = N := by
    rw [integral_finsetSum _ (fun i _ => hint i)]; simp [hnorm]
  rw [← this]; simp [hK, mul_comm]

/-- Pointwise Cauchy–Schwarz bound with a constant kernel (`‖Π‖_{2→∞}² ≤ K`). -/
theorem pointwise_bound (e : Fin N → X → ℝ) (K : ℝ) (hK : ∀ x, ∑ i, e i x ^ 2 = K)
    (a : Fin N → ℝ) (x : X) : (∑ i, a i * e i x) ^ 2 ≤ (∑ i, a i ^ 2) * K := by
  rw [← hK x]; exact sum_mul_sq_le_sq_mul_sq _ _ _

/-- Sharpness: the extremiser `a = e(x₀)` attains equality. -/
theorem pointwise_sharp (e : Fin N → X → ℝ) (K : ℝ) (hK : ∀ x, ∑ i, e i x ^ 2 = K) (x₀ : X) :
    (∑ i, e i x₀ * e i x₀) ^ 2 = (∑ i, e i x₀ ^ 2) * K := by
  have h : ∑ i, e i x₀ * e i x₀ = K := by rw [← hK x₀]; congr 1; ext i; ring
  rw [h, hK x₀]; ring

/-- **Sharp concentration–volume inequality**: if `w = Σ aᵢ eᵢ`, `w(x) ≠ 0`, then
`‖a‖² / w(x)² ≥ V / N` (`‖a‖² = ‖w‖₂²` by orthonormality). -/
theorem concentration (μ : Measure X) (e : Fin N → X → ℝ) (K : ℝ)
    (hint : ∀ i, Integrable (fun x => e i x ^ 2) μ) (hnorm : ∀ i, ∫ x, e i x ^ 2 ∂μ = 1)
    (hK : ∀ x, ∑ i, e i x ^ 2 = K) (hN : 0 < N) (a : Fin N → ℝ) (x : X)
    (hw : ∑ i, a i * e i x ≠ 0) :
    μ.real Set.univ / N ≤ (∑ i, a i ^ 2) / (∑ i, a i * e i x) ^ 2 := by
  have hc := kernel_const μ e K hint hnorm hK
  have hb := pointwise_bound e K hK a x
  have hpos : 0 < (∑ i, a i * e i x) ^ 2 := by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hV : 0 ≤ μ.real Set.univ := measureReal_nonneg
  rw [div_le_div_iff₀ hNr hpos, ← hc]
  have hK0 : 0 ≤ K := by rw [← hK x]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hb hV]

end FBS3R.Projector
