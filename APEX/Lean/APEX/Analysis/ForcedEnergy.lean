import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Forced dissipative systems: a priori norm bound

Let `E` be a real inner product space (no finite-dimensionality needed), `x : ℝ → E`
**differentiable everywhere** (we assume `HasDerivAt` at every `t`, instead of absolute
continuity), with
`x'(t) = -ν • A (x t) - Q (x t) + F t`, `ν ≥ 0`, `F` continuous, `⟪Q y, y⟫ = 0` for all `y`
(`A`, `Q : E → E` arbitrary, not necessarily linear).

* `norm_le_coercive`: if `λ‖y‖² ≤ ⟪A y, y⟫` for all `y` (`λ ≥ 0`), then for `t ≥ 0`, with `k = νλ`,
  `‖x t‖ ≤ e^{-kt} (‖x 0‖ + ∫₀ᵗ e^{ks} ‖F s‖ ds)`; and in the form
  `norm_le_coercive'`: `‖x t‖ ≤ e^{-kt}‖x 0‖ + ∫₀ᵗ e^{-k(t-s)} ‖F s‖ ds`.
* `norm_le_forced`: if `0 ≤ ⟪A y, y⟫` for all `y`, then `‖x t‖ ≤ ‖x 0‖ + ∫₀ᵗ ‖F s‖ ds` for `t ≥ 0`.

Proof: `y_ε = √(‖x‖² + ε²)` is differentiable, `(e^{ku} y_ε)' ≤ e^{ku}(‖F‖ + kε)`, monotonicity
(`antitone_of_deriv_nonpos`) and FTC, then `ε → 0`.
-/

open Real intervalIntegral

namespace APEX.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Coercive version with an explicit `exp` weight. -/
theorem norm_le_coercive (x : ℝ → E) (A Q : E → E) (F : ℝ → E) {ν lam : ℝ}
    (hν : 0 ≤ ν) (hlam : 0 ≤ lam)
    (hA : ∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A y) y) (hQ : ∀ y, inner ℝ (Q y) y = 0)
    (hF : Continuous F)
    (hx : ∀ t, HasDerivAt x (-(ν • A (x t)) - Q (x t) + F t) t) {t : ℝ} (ht : 0 ≤ t) :
    ‖x t‖ ≤ exp (-(ν * lam) * t) * (‖x 0‖ + ∫ s in (0)..t, exp (ν * lam * s) * ‖F s‖) := by
  set k := ν * lam with hk
  have hk0 : 0 ≤ k := mul_nonneg hν hlam
  set I := fun u => ∫ s in (0)..u, exp (k * s) * ‖F s‖
  have hIc : Continuous fun s => exp (k * s) * ‖F s‖ :=
    (continuous_exp.comp (continuous_const.mul continuous_id)).mul hF.norm
  have hI : ∀ u, HasDerivAt I (exp (k * u) * ‖F u‖) u := fun u =>
    (hIc.integral_hasStrictDerivAt 0 u).hasDerivAt
  -- main estimate for each ε > 0
  have key : ∀ ε > 0, ‖x t‖ ≤ exp (-k * t) * (‖x 0‖ + I t) + ε := by
    intro ε hε
    set y := fun u => √(‖x u‖ ^ 2 + ε ^ 2)
    have hSpos : ∀ u, 0 < ‖x u‖ ^ 2 + ε ^ 2 := fun u => by positivity
    have hy : ∀ u, HasDerivAt y (2 * inner ℝ (x u) (-(ν • A (x u)) - Q (x u) + F u)
        / (2 * √(‖x u‖ ^ 2 + ε ^ 2))) u := fun u =>
      ((hx u).norm_sq.add_const (ε ^ 2)).sqrt (hSpos u).ne'
    set h := fun u => exp (k * u) * y u - I u - ε * (exp (k * u) - 1)
    have hexp : ∀ u, HasDerivAt (fun u => exp (k * u)) (exp (k * u) * k) u := fun u => by
      simpa using ((hasDerivAt_id u).const_mul k).exp
    have hh : ∀ u, HasDerivAt h (exp (k * u) * k * y u + exp (k * u) *
        (2 * inner ℝ (x u) (-(ν • A (x u)) - Q (x u) + F u) / (2 * √(‖x u‖ ^ 2 + ε ^ 2)))
        - exp (k * u) * ‖F u‖ - ε * (exp (k * u) * k)) u := fun u =>
      (((hexp u).mul (hy u)).sub (hI u)).sub (((hexp u).sub_const 1).const_mul ε)
    have hderiv : ∀ u, deriv h u ≤ 0 := by
      intro u
      rw [(hh u).deriv]
      set S := √(‖x u‖ ^ 2 + ε ^ 2)
      have hS : 0 < S := sqrt_pos.2 (hSpos u)
      have hSsq : S ^ 2 = ‖x u‖ ^ 2 + ε ^ 2 := sq_sqrt (hSpos u).le
      have hxS : ‖x u‖ ≤ S := (le_sqrt (norm_nonneg _) (hSpos u).le).2 (by nlinarith)
      have hεS : ε ≤ S := (le_sqrt hε.le (hSpos u).le).2 (by nlinarith [sq_nonneg ‖x u‖])
      have hinner : inner ℝ (x u) (-(ν • A (x u)) - Q (x u) + F u)
          ≤ -k * ‖x u‖ ^ 2 + ‖x u‖ * ‖F u‖ := by
        rw [inner_add_right, inner_sub_right, inner_neg_right, real_inner_smul_right,
          real_inner_comm (Q (x u)), hQ]
        have h1 := hA (x u)
        have h2 := real_inner_le_norm (x u) (F u)
        rw [real_inner_comm] at h1
        have h3 := mul_le_mul_of_nonneg_left h1 hν
        rw [hk]; nlinarith
      -- k S + inner/S ≤ ‖F‖ + k ε
      have hmain : k * S + inner ℝ (x u) (-(ν • A (x u)) - Q (x u) + F u) / S
          ≤ ‖F u‖ + k * ε := by
        rw [← sub_nonneg]
        have : ‖F u‖ + k * ε - (k * S + inner ℝ (x u) (-(ν • A (x u)) - Q (x u) + F u) / S)
            = (k * (ε * S - ε ^ 2) + ‖F u‖ * (S - ‖x u‖)
              + (-k * ‖x u‖ ^ 2 + ‖x u‖ * ‖F u‖
                - inner ℝ (x u) (-(ν • A (x u)) - Q (x u) + F u))) / S := by
          field_simp
          nlinarith [hSsq]
        rw [this]
        refine div_nonneg ?_ hS.le
        have := mul_nonneg hk0 (mul_nonneg hε.le (sub_nonneg.2 hεS))
        have := mul_nonneg (norm_nonneg (F u)) (sub_nonneg.2 hxS)
        nlinarith
      have he := exp_pos (k * u)
      have : 2 * inner ℝ (x u) (-(ν • A (x u)) - Q (x u) + F u) / (2 * S)
          = inner ℝ (x u) (-(ν • A (x u)) - Q (x u) + F u) / S := by
        rw [mul_div_mul_left _ _ two_ne_zero]
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hmain he.le]
    have hanti := antitone_of_deriv_nonpos (fun u => (hh u).differentiableAt) hderiv
    have h0t := hanti ht
    simp only [h, I, y, mul_zero, exp_zero, one_mul, sub_self, integral_same, sub_zero,
      mul_zero] at h0t
    -- h0t : exp (k t) * y t - I t - ε (exp (k t) - 1) ≤ √(‖x 0‖² + ε²)
    have hy0 : √(‖x 0‖ ^ 2 + ε ^ 2) ≤ ‖x 0‖ + ε :=
      (sqrt_le_left (by positivity)).2 (by nlinarith [norm_nonneg (x 0)])
    have hyt : ‖x t‖ ≤ √(‖x t‖ ^ 2 + ε ^ 2) :=
      (le_sqrt (norm_nonneg _) (by positivity)).2 (by nlinarith)
    have hekt := exp_pos (k * t)
    have hmul : exp (-k * t) * exp (k * t) = 1 := by rw [← exp_add]; simp
    have hpos2 := exp_pos (-k * t)
    -- multiply h0t by exp(-kt)
    have := mul_le_mul_of_nonneg_left
      (show exp (k * t) * √(‖x t‖ ^ 2 + ε ^ 2) ≤ ‖x 0‖ + ε + I t + ε * (exp (k * t) - 1) by
        simp only [I]; linarith) hpos2.le
    have e1 : exp (-k * t) * (exp (k * t) * √(‖x t‖ ^ 2 + ε ^ 2)) = √(‖x t‖ ^ 2 + ε ^ 2) := by
      rw [← mul_assoc, hmul, one_mul]
    have e2 : exp (-k * t) * (‖x 0‖ + ε + I t + ε * (exp (k * t) - 1))
        = exp (-k * t) * (‖x 0‖ + I t) + ε := by
      have : exp (-k * t) * (‖x 0‖ + ε + I t + ε * (exp (k * t) - 1))
          = exp (-k * t) * (‖x 0‖ + I t) + ε * (exp (-k * t) * exp (k * t)) := by ring
      rw [this, hmul, mul_one]
    rw [e1, e2] at this
    linarith
  by_contra hcon
  push Not at hcon
  have := key ((‖x t‖ - exp (-k * t) * (‖x 0‖ + I t)) / 2) (by linarith)
  simp only [I] at this hcon
  linarith

/-- Coercive version, convolution form: `‖x t‖ ≤ e^{-νλt}‖x 0‖ + ∫₀ᵗ e^{-νλ(t-s)} ‖F s‖ ds`. -/
theorem norm_le_coercive' (x : ℝ → E) (A Q : E → E) (F : ℝ → E) {ν lam : ℝ}
    (hν : 0 ≤ ν) (hlam : 0 ≤ lam)
    (hA : ∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A y) y) (hQ : ∀ y, inner ℝ (Q y) y = 0)
    (hF : Continuous F)
    (hx : ∀ t, HasDerivAt x (-(ν • A (x t)) - Q (x t) + F t) t) {t : ℝ} (ht : 0 ≤ t) :
    ‖x t‖ ≤ exp (-(ν * lam) * t) * ‖x 0‖
      + ∫ s in (0)..t, exp (-(ν * lam) * (t - s)) * ‖F s‖ := by
  have h := norm_le_coercive x A Q F hν hlam hA hQ hF hx ht
  rw [mul_add, ← intervalIntegral.integral_const_mul] at h
  convert h using 3
  funext s
  rw [← mul_assoc, ← exp_add]; ring_nf

/-- **GATE-9 main bound.** `‖x t‖ ≤ ‖x 0‖ + ∫₀ᵗ ‖F s‖ ds` for `t ≥ 0`. -/
theorem norm_le_forced (x : ℝ → E) (A Q : E → E) (F : ℝ → E) {ν : ℝ} (hν : 0 ≤ ν)
    (hA : ∀ y, 0 ≤ inner ℝ (A y) y) (hQ : ∀ y, inner ℝ (Q y) y = 0)
    (hF : Continuous F)
    (hx : ∀ t, HasDerivAt x (-(ν • A (x t)) - Q (x t) + F t) t) {t : ℝ} (ht : 0 ≤ t) :
    ‖x t‖ ≤ ‖x 0‖ + ∫ s in (0)..t, ‖F s‖ := by
  have h := norm_le_coercive (lam := 0) x A Q F hν le_rfl (fun y => by simpa using hA y)
    hQ hF hx ht
  simpa using h

end APEX.Analysis

