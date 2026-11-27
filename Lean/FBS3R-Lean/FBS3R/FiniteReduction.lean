/-
# Finite spectral closure: energy no-go for finite reducing spaces (2026-09-20)

Source: *Finite-Dimensional Spectral Closure and a Relative Forced Singular Branch for
Navier–Stokes on the Round Three-Sphere*.  The paper states: for a quadratic evolution
`ẋ + νAx + Q(x,x) = F(t)` with energy-cancelling `Q` (`⟪Q(x,x),x⟫ = 0`) and nonnegative `A`,
no exact finite reducing space carries bounded-energy blow-up under integrable forcing.

Machine-checked here, in any real inner-product space (in particular on any finite modal
space `W`), for continuous forcing:
* `energy_bound` : every solution on `[0,T]` obeys
  `‖x(t)‖² + 1 ≤ (‖x(0)‖² + 1) · exp(∫₀ᵗ ‖F‖)`;
* `no_blowup` : hence `‖x‖` stays bounded on `[0,T]` by a constant depending only on
  `‖x(0)‖` and `∫₀ᵀ ‖F‖` — no finite-time blow-up inside a reducing space.

This does not touch the regularity of the full Navier–Stokes equation (open problem); it is
the finite-dimensional obstruction the paper uses, and the forcing is assumed continuous
(the paper allows `L¹`).
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace FBS3R.FiniteReduction

open Real Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

theorem energy_bound (A : E → E) (Q : E → E) (ν T : ℝ) (hν : 0 ≤ ν)
    (hA : ∀ v, 0 ≤ ⟪A v, v⟫) (hQ : ∀ v, ⟪Q v, v⟫ = 0)
    (F : ℝ → E) (hF : Continuous F) (x : ℝ → E)
    (hx : ∀ t ∈ Icc 0 T, HasDerivAt x (-(ν • A (x t)) - Q (x t) + F t) t) :
    ∀ t ∈ Icc 0 T,
      ‖x t‖ ^ 2 + 1 ≤ (‖x 0‖ ^ 2 + 1) * exp (∫ s in (0:ℝ)..t, ‖F s‖) := by
  set I : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, ‖F s‖
  have hFn : Continuous fun s => ‖F s‖ := hF.norm
  have hI : ∀ t, HasDerivAt I ‖F t‖ t := fun t => (hFn.integral_hasStrictDerivAt 0 t).hasDerivAt
  set φ : ℝ → ℝ := fun t => (‖x t‖ ^ 2 + 1) * exp (-I t)
  set φ' : ℝ → ℝ := fun t =>
    2 * ⟪x t, -(ν • A (x t)) - Q (x t) + F t⟫ * exp (-I t)
      + (‖x t‖ ^ 2 + 1) * (exp (-I t) * -‖F t‖)
  have hφ : ∀ t ∈ Icc 0 T, HasDerivAt φ (φ' t) t := by
    intro t ht
    have h1 := ((hx t ht).norm_sq).add_const 1
    have h2 := ((hI t).neg).exp
    exact h1.mul h2
  have hφ'_nonpos : ∀ t ∈ Icc 0 T, φ' t ≤ 0 := by
    intro t _
    have hin : ⟪x t, -(ν • A (x t)) - Q (x t) + F t⟫ ≤ ‖x t‖ * ‖F t‖ := by
      rw [inner_add_right, inner_sub_right, inner_neg_right, inner_smul_right,
        real_inner_comm (A (x t)) (x t), real_inner_comm (Q (x t)) (x t), hQ]
      have h1 : 0 ≤ ν * ⟪A (x t), x t⟫ := mul_nonneg hν (hA _)
      have h2 : ⟪x t, F t⟫ ≤ ‖x t‖ * ‖F t‖ := real_inner_le_norm _ _
      linarith
    have hamgm : 2 * (‖x t‖ * ‖F t‖) ≤ (‖x t‖ ^ 2 + 1) * ‖F t‖ := by
      have := sq_nonneg (‖x t‖ - 1); have := norm_nonneg (F t); nlinarith
    have he : 0 < exp (-I t) := exp_pos _
    simp only [φ']
    nlinarith
  have hanti : AntitoneOn φ (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
    · intro t ht; exact (hφ t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hφ t (interior_subset ht)).hasDerivWithinAt
    · intro t ht; exact hφ'_nonpos t (interior_subset ht)
  intro t ht
  by_cases hT : 0 ≤ T
  · have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    have := hanti h0 ht ht.1
    simp only [φ, I, intervalIntegral.integral_same, neg_zero, exp_zero, mul_one] at this
    have hpos : 0 < exp (-(∫ s in (0:ℝ)..t, ‖F s‖)) := exp_pos _
    calc ‖x t‖ ^ 2 + 1
        = (‖x t‖ ^ 2 + 1) * exp (-(∫ s in (0:ℝ)..t, ‖F s‖)) * exp (∫ s in (0:ℝ)..t, ‖F s‖) := by
          rw [mul_assoc, ← exp_add]; simp
      _ ≤ (‖x 0‖ ^ 2 + 1) * exp (∫ s in (0:ℝ)..t, ‖F s‖) := by
          gcongr
  · exact absurd (ht.1.trans ht.2) hT

theorem no_blowup (A : E → E) (Q : E → E) (ν T : ℝ) (hν : 0 ≤ ν)
    (hA : ∀ v, 0 ≤ ⟪A v, v⟫) (hQ : ∀ v, ⟪Q v, v⟫ = 0)
    (F : ℝ → E) (hF : Continuous F) (x : ℝ → E)
    (hx : ∀ t ∈ Icc 0 T, HasDerivAt x (-(ν • A (x t)) - Q (x t) + F t) t) :
    ∀ t ∈ Icc 0 T,
      ‖x t‖ ^ 2 ≤ (‖x 0‖ ^ 2 + 1) * exp (∫ s in (0:ℝ)..T, ‖F s‖) := by
  intro t ht
  have h := energy_bound A Q ν T hν hA hQ F hF x hx t ht
  have hmono : (∫ s in (0:ℝ)..t, ‖F s‖) ≤ ∫ s in (0:ℝ)..T, ‖F s‖ := by
    exact intervalIntegral.integral_mono_interval (le_refl (0:ℝ)) ht.1 ht.2
      (MeasureTheory.ae_of_all _ (fun s => norm_nonneg (F s))) (hF.norm.intervalIntegrable 0 T)
  have : exp (∫ s in (0:ℝ)..t, ‖F s‖) ≤ exp (∫ s in (0:ℝ)..T, ‖F s‖) := exp_le_exp.mpr hmono
  have hp : 0 ≤ ‖x 0‖ ^ 2 + 1 := by positivity
  calc ‖x t‖ ^ 2 ≤ ‖x t‖ ^ 2 + 1 := by linarith
    _ ≤ (‖x 0‖ ^ 2 + 1) * exp (∫ s in (0:ℝ)..t, ‖F s‖) := h
    _ ≤ (‖x 0‖ ^ 2 + 1) * exp (∫ s in (0:ℝ)..T, ‖F s‖) := mul_le_mul_of_nonneg_left this hp

end FBS3R.FiniteReduction
