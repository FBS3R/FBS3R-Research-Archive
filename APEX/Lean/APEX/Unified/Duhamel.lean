import APEX.Unified.Consistency
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Duhamel formula and defect bounds for scale consistency (bounded generators)

Builds on `APEX.Unified.Consistency` (where `R ∘ A = A' ∘ R ↔ ∀ t, R ∘ e^{tA} = e^{tA'} ∘ R`
is proved). Here we quantify the *approximate* case. Setting: real Banach spaces `E, F`,
bounded `R : E →L[ℝ] F`, `A : E →L[ℝ] E`, `A' : F →L[ℝ] F`, `e^{tA} = NormedSpace.exp (t • A)`,
defect `D = R ∘ A − A' ∘ R`. All compositions are `ContinuousLinearMap.comp`.

## Main results
1. `duhamel` (exact identity, Bochner interval integral):
   `R e^{tA} − e^{tA'} R = ∫₀ᵗ e^{(t−s)A'} ∘ D ∘ e^{sA} ds` for every real `t`.
   Proof: derivative of `s ↦ e^{(t−s)A'} R e^{sA}` + FTC.
2. `norm_sub_le_of_contraction`: `t ≥ 0`, `‖e^{sA}‖ ≤ 1`, `‖e^{sA'}‖ ≤ 1` for `s ∈ [0,t]` ⇒
   `‖R e^{tA} − e^{tA'} R‖ ≤ t ‖D‖`. General majorant form: `norm_sub_le_integral`.
3. Decay: if `‖e^{sA}‖ ≤ M e^{−λs}`, `‖e^{sA'}‖ ≤ M' e^{−λ's}` on `[0,t]`:
   * `norm_sub_le_decay`: `‖…‖ ≤ M M' ‖D‖ ∫₀ᵗ e^{−λ'(t−s)} e^{−λs} ds`;
   * `norm_sub_le_decay_of_ne` (`λ ≠ λ'`): `≤ M M' ‖D‖ (e^{−λt} − e^{−λ't})/(λ' − λ)`;
   * `norm_sub_le_decay_of_eq` (`λ = λ'`): `≤ M M' ‖D‖ t e^{−λt}`;
   * `norm_sub_le_decay_min` (`M, M' ≥ 0`): `≤ M M' ‖D‖ t e^{−min(λ,λ') t}`;
   * `norm_sub_le_uniform` (`M, M' ≥ 0`, `λ ≥ 0`, `λ' > 0`): `≤ M M' ‖D‖ / λ'`, uniformly in `t`.
   Scalar integrals: `integral_exp_mul_exp_of_ne`, `integral_exp_mul_exp_self`,
   `integral_exp_mul_exp_le`. Only the global (whole-space) decay version is done; decay on
   invariant subspaces is not formalised.
4. * `norm_exp_comp_le_gap`: if moreover `‖e^{tA}‖ ≤ e^{−Δt}`, then
     `‖e^{tA'} ∘ R‖ ≤ ‖R‖ e^{−Δt} + t ‖D‖` (approximate decay transfer on the range of `R`;
     *not* a spectral-gap theorem for `A'`).
   * Multi-scale accumulation `norm_chain_defect_le`: for `R_k : E_k →L E_{k+1}`, generators
     `A_k` with contractive semigroups on `[0,t]` (`k ≤ n`), `D_k = R_k A_k − A_{k+1} R_k` and
     `chain R n = R_{n−1} ∘ ⋯ ∘ R_0`:
     `‖chain R n ∘ e^{tA_0} − e^{tA_n} ∘ chain R n‖ ≤ t ∑_{k<n} ‖D_k‖ ∏_{j<n, j≠k} ‖R_j‖`;
     `norm_chain_defect_le_sum`: if all `‖R_j‖ ≤ 1`, the bound is `t ∑_{k<n} ‖D_k‖`.
5. Finite dimensions: `fd_norm_sub_le_of_contraction` (any real-linear `R, L, L'` between
   finite-dimensional real normed spaces, with any norm), and `matrix_superop_norm_sub_le`
   for superoperators on `M_d(ℂ)` with the Hilbert–Schmidt norm, encoded as
   `EuclideanSpace ℂ (d × d)` (e.g. GKSL generators `L, L'` and a coarse-graining map `R`).
   Contractivity of the semigroups in that norm is a **hypothesis**. Nothing about complete
   positivity, trace preservation, GKSL structure or trace-norm contractivity is proved.

## Caveat
These are statements about linear dynamics and an arbitrary linear map `R`. Small defect
(approximate scale consistency) is a *consistency/approximation* property; it is not by itself
a physical law and singles out no particular physical theory.
-/

open NormedSpace

namespace APEX.Unified.Duhamel

section Operator
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The consistency defect `D = R A − A' R`. -/
def defect (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) : E →L[ℝ] F :=
  R.comp A - A'.comp R

/-- The Duhamel integrand `s ↦ exp((t−s)A') ∘ D ∘ exp(sA)`. -/
noncomputable def integrand (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) (t s : ℝ) :
    E →L[ℝ] F :=
  (exp ((t - s) • A')).comp ((defect R A A').comp (exp (s • A)))

theorem hasDerivAt_exp_sub_smul (A' : F →L[ℝ] F) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => exp ((t - u) • A')) (-(exp ((t - s) • A') * A')) s := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) A' (t - s)
  have h2 : HasDerivAt (fun u : ℝ => t - u) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub t
  have := h1.scomp s h2
  simpa [Function.comp_def] using this

theorem hasDerivAt_duhamel (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => (exp ((t - u) • A')).comp (R.comp (exp (u • A))))
      (integrand R A A' t s) s := by
  have hA := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s
  have hRA : HasDerivAt (fun u : ℝ => R.comp (exp (u • A))) (R.comp (A * exp (s • A))) s :=
    (HasDerivAt.clm_comp (hasDerivAt_const s R) hA).congr_deriv (by simp)
  have := HasDerivAt.clm_comp (hasDerivAt_exp_sub_smul A' t s) hRA
  convert this using 1
  ext x
  simp [integrand, defect, ContinuousLinearMap.mul_def]
  abel

theorem continuous_integrand (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) (t : ℝ) :
    Continuous (integrand R A A' t) := by
  have c1 : Continuous (fun s : ℝ => exp (s • A)) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_smul_const (𝕂 := ℝ) A s).continuousAt
  have c2 : Continuous (fun s : ℝ => exp ((t - s) • A')) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_sub_smul A' t s).continuousAt
  exact c2.clm_comp (continuous_const.clm_comp c1)

/-- **Duhamel identity** for bounded generators:
`R e^{tA} − e^{tA'} R = ∫₀ᵗ e^{(t−s)A'} (R A − A' R) e^{sA} ds`. -/
theorem duhamel (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) (t : ℝ) :
    R.comp (exp (t • A)) - (exp (t • A')).comp R =
      ∫ s in (0:ℝ)..t, (exp ((t - s) • A')).comp ((R.comp A - A'.comp R).comp (exp (s • A))) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => (exp ((t - u) • A')).comp (R.comp (exp (u • A))))
    (a := 0) (b := t) (fun s _ => hasDerivAt_duhamel R A A' t s)
    ((continuous_integrand R A A' t).intervalIntegrable 0 t)
  simp only [integrand, defect] at h
  rw [h]
  simp [ContinuousLinearMap.one_def]


omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_integrand_le (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) (t s : ℝ) :
    ‖integrand R A A' t s‖ ≤ ‖exp ((t - s) • A')‖ * ‖defect R A A'‖ * ‖exp (s • A)‖ := by
  unfold integrand
  calc _ ≤ ‖exp ((t - s) • A')‖ * ‖(defect R A A').comp (exp (s • A))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖exp ((t - s) • A')‖ * (‖defect R A A'‖ * ‖exp (s • A)‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by ring

/-- **Contraction bound.** If both semigroups are contractive on `[0,t]`, then
`‖R e^{tA} − e^{tA'} R‖ ≤ t ‖R A − A' R‖`. -/
theorem norm_sub_le_of_contraction (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) {t : ℝ}
    (ht : 0 ≤ t) (hA : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A)‖ ≤ 1)
    (hA' : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A')‖ ≤ 1) :
    ‖R.comp (exp (t • A)) - (exp (t • A')).comp R‖ ≤ t * ‖R.comp A - A'.comp R‖ := by
  rw [duhamel]
  have key : ∀ s ∈ Set.uIoc (0:ℝ) t, ‖integrand R A A' t s‖ ≤ ‖defect R A A'‖ := by
    intro s hs
    rw [Set.uIoc_of_le ht] at hs
    have h1 := hA s ⟨hs.1.le, hs.2⟩
    have h2 := hA' (t - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    calc _ ≤ ‖exp ((t - s) • A')‖ * ‖defect R A A'‖ * ‖exp (s • A)‖ := norm_integrand_le _ _ _ _ _
      _ ≤ 1 * ‖defect R A A'‖ * 1 := by gcongr
      _ = _ := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const key
  simp only [integrand, defect, sub_zero, abs_of_nonneg ht] at this
  linarith

/-- Pointwise-in-time version with arbitrary bounds:
`‖R e^{tA} − e^{tA'} R‖ ≤ ∫₀ᵗ ‖e^{(t−s)A'}‖ ‖D‖ ‖e^{sA}‖ ds`-type estimate with given majorants. -/
theorem norm_sub_le_integral (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) {t : ℝ}
    (ht : 0 ≤ t) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hA : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A)‖ ≤ f s)
    (hA' : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A')‖ ≤ g s) :
    ‖R.comp (exp (t • A)) - (exp (t • A')).comp R‖ ≤
      ‖R.comp A - A'.comp R‖ * ∫ s in (0:ℝ)..t, g (t - s) * f s := by
  rw [duhamel, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le ht (Filter.Eventually.of_forall ?_) ?_
  · intro s hs
    have h1 := hA s ⟨hs.1.le, hs.2⟩
    have h2 := hA' (t - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    calc _ ≤ ‖exp ((t - s) • A')‖ * ‖defect R A A'‖ * ‖exp (s • A)‖ := norm_integrand_le _ _ _ _ _
      _ ≤ g (t - s) * ‖defect R A A'‖ * f s :=
          mul_le_mul (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) h1 (norm_nonneg _)
            (mul_nonneg ((norm_nonneg _).trans h2) (norm_nonneg _))
      _ = _ := by simp only [defect]; ring
  · exact (continuous_const.mul ((hg.comp (continuous_const.sub continuous_id)).mul hf)).intervalIntegrable _ _

end Operator

section ScalarIntegrals

theorem integral_exp_mul_exp_of_ne {a b : ℝ} (t : ℝ) (hab : a ≠ b) :
    ∫ s in (0:ℝ)..t, Real.exp (-(b * (t - s))) * Real.exp (-(a * s)) =
      (Real.exp (-(a * t)) - Real.exp (-(b * t))) / (b - a) := by
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hfun : (fun s : ℝ => Real.exp (-(b * (t - s))) * Real.exp (-(a * s))) =
      fun s => Real.exp ((b - a) * s - b * t) := by
    funext s; rw [← Real.exp_add]; congr 1; ring
  have hd : ∀ s ∈ Set.uIcc (0:ℝ) t, HasDerivAt (fun s => Real.exp ((b - a) * s - b * t) / (b - a))
      (Real.exp ((b - a) * s - b * t)) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => (b - a) * s - b * t) (b - a) s := by
      simpa using ((hasDerivAt_id s).const_mul (b - a)).sub_const (b * t)
    have := (HasDerivAt.exp h1).div_const (b - a)
    convert this using 1
    field_simp
  rw [hfun, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
      continuous_const)).intervalIntegrable _ _)]
  rw [div_sub_div_same]
  congr 2 <;> ring_nf

theorem integral_exp_mul_exp_self (a t : ℝ) :
    ∫ s in (0:ℝ)..t, Real.exp (-(a * (t - s))) * Real.exp (-(a * s)) = t * Real.exp (-(a * t)) := by
  have hfun : (fun s : ℝ => Real.exp (-(a * (t - s))) * Real.exp (-(a * s))) =
      fun _ => Real.exp (-(a * t)) := by
    funext s; rw [← Real.exp_add]; congr 1; ring
  rw [hfun]; simp

theorem integral_exp_mul_exp_le {a b : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0:ℝ)..t, Real.exp (-(b * (t - s))) * Real.exp (-(a * s)) ≤
      t * Real.exp (-(min a b * t)) := by
  have h : ∀ s ∈ Set.Icc (0:ℝ) t,
      Real.exp (-(b * (t - s))) * Real.exp (-(a * s)) ≤ Real.exp (-(min a b * t)) := by
    intro s hs
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : min a b * (t - s) ≤ b * (t - s) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith [hs.2])
    have h2 : min a b * s ≤ a * s := mul_le_mul_of_nonneg_right (min_le_left _ _) hs.1
    nlinarith
  have hc : Continuous (fun s : ℝ => Real.exp (-(b * (t - s))) * Real.exp (-(a * s))) := by
    fun_prop
  have := intervalIntegral.integral_mono_on ht (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 t) h
  simpa [mul_comm] using this

end ScalarIntegrals

section Decay
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Decay bound.** If `‖e^{sA}‖ ≤ M e^{−λ s}` and `‖e^{sA'}‖ ≤ M' e^{−λ' s}` on `[0,t]`, then
`‖R e^{tA} − e^{tA'} R‖ ≤ M M' ‖D‖ ∫₀ᵗ e^{−λ'(t−s)} e^{−λ s} ds`. -/
theorem norm_sub_le_decay (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) {t : ℝ}
    (ht : 0 ≤ t) (M M' lam lam' : ℝ)
    (hA : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A)‖ ≤ M * Real.exp (-(lam * s)))
    (hA' : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A')‖ ≤ M' * Real.exp (-(lam' * s))) :
    ‖R.comp (exp (t • A)) - (exp (t • A')).comp R‖ ≤
      M * M' * ‖R.comp A - A'.comp R‖ *
        ∫ s in (0:ℝ)..t, Real.exp (-(lam' * (t - s))) * Real.exp (-(lam * s)) := by
  have h := norm_sub_le_integral R A A' ht (fun s => M * Real.exp (-(lam * s)))
    (fun s => M' * Real.exp (-(lam' * s))) (by fun_prop) (by fun_prop) hA hA'
  have hfun : (fun s : ℝ => M' * Real.exp (-(lam' * (t - s))) * (M * Real.exp (-(lam * s)))) =
      fun s => (M * M') * (Real.exp (-(lam' * (t - s))) * Real.exp (-(lam * s))) := by
    funext s; ring
  simp only [hfun, intervalIntegral.integral_const_mul] at h
  linarith

/-- Closed form of the decay bound for `λ ≠ λ'`. -/
theorem norm_sub_le_decay_of_ne (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) {t : ℝ}
    (ht : 0 ≤ t) (M M' lam lam' : ℝ) (hne : lam ≠ lam')
    (hA : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A)‖ ≤ M * Real.exp (-(lam * s)))
    (hA' : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A')‖ ≤ M' * Real.exp (-(lam' * s))) :
    ‖R.comp (exp (t • A)) - (exp (t • A')).comp R‖ ≤
      M * M' * ‖R.comp A - A'.comp R‖ *
        ((Real.exp (-(lam * t)) - Real.exp (-(lam' * t))) / (lam' - lam)) := by
  rw [← integral_exp_mul_exp_of_ne t hne]
  exact norm_sub_le_decay R A A' ht M M' lam lam' hA hA'

/-- Closed form of the decay bound for equal rates `λ = λ'`: `M M' ‖D‖ t e^{−λ t}`. -/
theorem norm_sub_le_decay_of_eq (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) {t : ℝ}
    (ht : 0 ≤ t) (M M' lam : ℝ)
    (hA : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A)‖ ≤ M * Real.exp (-(lam * s)))
    (hA' : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A')‖ ≤ M' * Real.exp (-(lam * s))) :
    ‖R.comp (exp (t • A)) - (exp (t • A')).comp R‖ ≤
      M * M' * ‖R.comp A - A'.comp R‖ * (t * Real.exp (-(lam * t))) := by
  rw [← integral_exp_mul_exp_self lam t]
  exact norm_sub_le_decay R A A' ht M M' lam lam hA hA'

/-- Uniform-in-rates bound: `‖R e^{tA} − e^{tA'} R‖ ≤ M M' ‖D‖ t e^{−min(λ,λ') t}`. -/
theorem norm_sub_le_decay_min (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) {t : ℝ}
    (ht : 0 ≤ t) (M M' lam lam' : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hA : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A)‖ ≤ M * Real.exp (-(lam * s)))
    (hA' : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A')‖ ≤ M' * Real.exp (-(lam' * s))) :
    ‖R.comp (exp (t • A)) - (exp (t • A')).comp R‖ ≤
      M * M' * ‖R.comp A - A'.comp R‖ * (t * Real.exp (-(min lam lam' * t))) :=
  (norm_sub_le_decay R A A' ht M M' lam lam' hA hA').trans
    (mul_le_mul_of_nonneg_left (integral_exp_mul_exp_le ht) (by positivity))

/-- **Time-uniform bound.** If the coarse semigroup decays strictly (`λ' > 0`) and the fine one
does not grow (`λ ≥ 0`), the defect stays bounded for all times:
`‖R e^{tA} − e^{tA'} R‖ ≤ M M' ‖D‖ / λ'`. -/
theorem norm_sub_le_uniform (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) {t : ℝ}
    (ht : 0 ≤ t) (M M' lam lam' : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hlam : 0 ≤ lam)
    (hlam' : 0 < lam')
    (hA : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A)‖ ≤ M * Real.exp (-(lam * s)))
    (hA' : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A')‖ ≤ M' * Real.exp (-(lam' * s))) :
    ‖R.comp (exp (t • A)) - (exp (t • A')).comp R‖ ≤ M * M' * ‖R.comp A - A'.comp R‖ / lam' := by
  have h := norm_sub_le_decay R A A' ht M M' lam lam' hA hA'
  have hc1 : Continuous (fun s : ℝ => Real.exp (-(lam' * (t - s))) * Real.exp (-(lam * s))) := by
    fun_prop
  have hc2 : Continuous (fun s : ℝ => Real.exp (-(lam' * (t - s))) * Real.exp (-(0 * s))) := by
    fun_prop
  have hmono := intervalIntegral.integral_mono_on ht
    (hc1.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    (hc2.intervalIntegrable (μ := MeasureTheory.volume) 0 t) (fun s hs => by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Real.exp_le_exp.2
      nlinarith [hs.1])
  rw [integral_exp_mul_exp_of_ne t (ne_of_lt hlam')] at hmono
  have hb : (Real.exp (-(0 * t)) - Real.exp (-(lam' * t))) / (lam' - 0) ≤ 1 / lam' := by
    rw [sub_zero]
    apply div_le_div_of_nonneg_right _ hlam'.le
    simp [(Real.exp_pos _).le]
  have hK : 0 ≤ M * M' * ‖R.comp A - A'.comp R‖ := by positivity
  calc _ ≤ _ := h
    _ ≤ M * M' * ‖R.comp A - A'.comp R‖ * (1 / lam') :=
        mul_le_mul_of_nonneg_left (hmono.trans hb) hK
    _ = _ := by ring

/-- **Approximate gap transfer.** If the fine semigroup has decay `‖e^{tA}‖ ≤ e^{−Δ t}` (and both
semigroups are contractive on `[0,t]`), then the coarse dynamics restricted to the image of `R`
decays up to the defect: `‖e^{tA'} ∘ R‖ ≤ ‖R‖ e^{−Δ t} + t ‖R A − A' R‖`.
(This is *not* a spectral-gap statement for `A'` on all of `F`.) -/
theorem norm_exp_comp_le_gap (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) {t Δ : ℝ}
    (ht : 0 ≤ t) (hgap : ‖exp (t • A)‖ ≤ Real.exp (-(Δ * t)))
    (hA : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A)‖ ≤ 1)
    (hA' : ∀ s ∈ Set.Icc 0 t, ‖exp (s • A')‖ ≤ 1) :
    ‖(exp (t • A')).comp R‖ ≤ ‖R‖ * Real.exp (-(Δ * t)) + t * ‖R.comp A - A'.comp R‖ := by
  have h := norm_sub_le_of_contraction R A A' ht hA hA'
  have e : (exp (t • A')).comp R =
      R.comp (exp (t • A)) - (R.comp (exp (t • A)) - (exp (t • A')).comp R) := by abel
  rw [e]
  calc _ ≤ ‖R.comp (exp (t • A))‖ + ‖R.comp (exp (t • A)) - (exp (t • A')).comp R‖ :=
        norm_sub_le _ _
    _ ≤ ‖R‖ * Real.exp (-(Δ * t)) + t * ‖R.comp A - A'.comp R‖ :=
        add_le_add ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left hgap (norm_nonneg _))) h

end Decay

section MultiScale
/-! ### Multi-scale error accumulation -/
variable {E : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)] [∀ k, NormedSpace ℝ (E k)]

/-- The composite coarse-graining `R_{n−1} ∘ ⋯ ∘ R_0 : E 0 → E n`. -/
noncomputable def chain (R : ∀ k, E k →L[ℝ] E (k + 1)) : (n : ℕ) → E 0 →L[ℝ] E n
  | 0 => ContinuousLinearMap.id ℝ (E 0)
  | n + 1 => (R n).comp (chain R n)

theorem norm_chain_le (R : ∀ k, E k →L[ℝ] E (k + 1)) (n : ℕ) :
    ‖chain R n‖ ≤ ∏ j ∈ Finset.range n, ‖R j‖ := by
  induction n with
  | zero => simpa [chain] using ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [Finset.prod_range_succ, chain, mul_comm]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

theorem sum_erase_succ (d r : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), d k * ∏ j ∈ (Finset.range (n + 1)).erase k, r j =
      r n * ∑ k ∈ Finset.range n, d k * ∏ j ∈ (Finset.range n).erase k, r j +
        d n * ∏ j ∈ Finset.range n, r j := by
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hkn : n ≠ k := by
      have := Finset.mem_range.1 hk; omega
    rw [Finset.range_add_one, Finset.erase_insert_of_ne hkn,
      Finset.prod_insert (by simp)]
    ring
  · rw [Finset.range_add_one, Finset.erase_insert (by simp)]

variable [∀ k, CompleteSpace (E k)]

/-- **Multi-scale accumulation.** With coarse-grainings `R_k : E_k → E_{k+1}`, generators `A_k`
whose semigroups are contractive on `[0,t]` for `k ≤ n`, and defects `D_k = R_k A_k − A_{k+1} R_k`:
`‖R_{n−1}⋯R_0 e^{tA_0} − e^{tA_n} R_{n−1}⋯R_0‖ ≤ t ∑_{k<n} ‖D_k‖ ∏_{j<n, j≠k} ‖R_j‖`. -/
theorem norm_chain_defect_le (R : ∀ k, E k →L[ℝ] E (k + 1)) (A : ∀ k, E k →L[ℝ] E k)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ k ≤ n, ∀ s ∈ Set.Icc 0 t, ‖exp (s • A k)‖ ≤ 1) :
    ‖(chain R n).comp (exp (t • A 0)) - (exp (t • A n)).comp (chain R n)‖ ≤
      t * ∑ k ∈ Finset.range n, ‖(R k).comp (A k) - (A (k + 1)).comp (R k)‖ *
        ∏ j ∈ (Finset.range n).erase k, ‖R j‖ := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    have ih' := ih (fun k hk => hA k (Nat.le_succ_of_le hk))
    have hstep := norm_sub_le_of_contraction (R n) (A n) (A (n + 1)) ht
      (hA n (Nat.le_succ n)) (hA (n + 1) le_rfl)
    have hsplit : (chain R (n + 1)).comp (exp (t • A 0)) - (exp (t • A (n + 1))).comp (chain R (n + 1))
        = (R n).comp ((chain R n).comp (exp (t • A 0)) - (exp (t • A n)).comp (chain R n)) +
          ((R n).comp (exp (t • A n)) - (exp (t • A (n + 1))).comp (R n)).comp (chain R n) := by
      ext x; simp [chain]
    rw [hsplit, sum_erase_succ]
    calc _ ≤ ‖R n‖ * ‖(chain R n).comp (exp (t • A 0)) - (exp (t • A n)).comp (chain R n)‖ +
          ‖(R n).comp (exp (t • A n)) - (exp (t • A (n + 1))).comp (R n)‖ * ‖chain R n‖ :=
          (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _))
      _ ≤ ‖R n‖ * (t * ∑ k ∈ Finset.range n, ‖(R k).comp (A k) - (A (k + 1)).comp (R k)‖ *
            ∏ j ∈ (Finset.range n).erase k, ‖R j‖) +
          (t * ‖(R n).comp (A n) - (A (n + 1)).comp (R n)‖) * ∏ j ∈ Finset.range n, ‖R j‖ :=
          add_le_add (mul_le_mul_of_nonneg_left ih' (norm_nonneg _))
            (mul_le_mul hstep (norm_chain_le R n) (norm_nonneg _) (by positivity))
      _ = _ := by ring

/-- Corollary for norm-nonincreasing coarse-grainings (`‖R_j‖ ≤ 1`):
the error is at most `t ∑_{k<n} ‖D_k‖`. -/
theorem norm_chain_defect_le_sum (R : ∀ k, E k →L[ℝ] E (k + 1)) (A : ∀ k, E k →L[ℝ] E k)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (hR : ∀ k, ‖R k‖ ≤ 1)
    (hA : ∀ k ≤ n, ∀ s ∈ Set.Icc 0 t, ‖exp (s • A k)‖ ≤ 1) :
    ‖(chain R n).comp (exp (t • A 0)) - (exp (t • A n)).comp (chain R n)‖ ≤
      t * ∑ k ∈ Finset.range n, ‖(R k).comp (A k) - (A (k + 1)).comp (R k)‖ := by
  refine (norm_chain_defect_le R A n ht hA).trans (mul_le_mul_of_nonneg_left ?_ ht)
  apply Finset.sum_le_sum
  intro k _
  calc _ ≤ ‖(R k).comp (A k) - (A (k + 1)).comp (R k)‖ * 1 :=
        mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
          (fun j _ => hR j)) (norm_nonneg _)
    _ = _ := mul_one _

end MultiScale

section FiniteDim
/-! ### Finite-dimensional state spaces (e.g. matrix algebras with a chosen norm) -/
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Contraction bound for arbitrary *linear* maps between finite-dimensional real normed spaces
(any norm): applies e.g. to a GKSL generator `L` on `M_n(ℂ)` viewed as a real vector space. -/
theorem fd_norm_sub_le_of_contraction (R : V →ₗ[ℝ] W) (L : V →ₗ[ℝ] V) (L' : W →ₗ[ℝ] W) {t : ℝ}
    (ht : 0 ≤ t)
    (hL : ∀ s ∈ Set.Icc 0 t, ‖exp (s • LinearMap.toContinuousLinearMap L)‖ ≤ 1)
    (hL' : ∀ s ∈ Set.Icc 0 t, ‖exp (s • LinearMap.toContinuousLinearMap L')‖ ≤ 1) :
    ‖(LinearMap.toContinuousLinearMap R).comp (exp (t • LinearMap.toContinuousLinearMap L)) -
        (exp (t • LinearMap.toContinuousLinearMap L')).comp (LinearMap.toContinuousLinearMap R)‖ ≤
      t * ‖LinearMap.toContinuousLinearMap (R ∘ₗ L - L' ∘ₗ R)‖ := by
  have := FiniteDimensional.completeSpace ℝ V
  have := FiniteDimensional.completeSpace ℝ W
  have h := norm_sub_le_of_contraction (LinearMap.toContinuousLinearMap R)
    (LinearMap.toContinuousLinearMap L) (LinearMap.toContinuousLinearMap L') ht hL hL'
  have he : LinearMap.toContinuousLinearMap (R ∘ₗ L - L' ∘ₗ R) =
      (LinearMap.toContinuousLinearMap R).comp (LinearMap.toContinuousLinearMap L) -
        (LinearMap.toContinuousLinearMap L').comp (LinearMap.toContinuousLinearMap R) := by
    ext x; simp
  rwa [he]

end FiniteDim

section Matrices
/-! `M_d(ℂ)` with the Hilbert–Schmidt (Frobenius) norm is modelled as `EuclideanSpace ℂ (d × d)`
(entries `X (i, j)`, norm `(∑ |X_{ij}|²)^{1/2}`), regarded as a real normed space. (Mathlib's
`Matrix.frobeniusNormedAddCommGroup` is a non-instance whose topology is not reducibly the global
`Matrix` topology, so bundled operator norms on `Matrix d d ℂ →L[ℝ] _` do not synthesize; this
encoding avoids that.) -/

/-- The contraction bound for real-linear superoperators on Hilbert–Schmidt matrix spaces:
`L : M_d → M_d`, `L' : M_e → M_e` (e.g. GKSL generators) and any linear `R : M_d → M_e`
(e.g. a coarse-graining channel such as a partial trace). Contractivity of the generated
semigroups in the Hilbert–Schmidt operator norm is a *hypothesis*, not proved here. -/
theorem matrix_superop_norm_sub_le {d e : Type*} [Fintype d] [Fintype e]
    (R : EuclideanSpace ℂ (d × d) →ₗ[ℝ] EuclideanSpace ℂ (e × e))
    (L : EuclideanSpace ℂ (d × d) →ₗ[ℝ] EuclideanSpace ℂ (d × d))
    (L' : EuclideanSpace ℂ (e × e) →ₗ[ℝ] EuclideanSpace ℂ (e × e)) {t : ℝ} (ht : 0 ≤ t)
    (hL : ∀ s ∈ Set.Icc 0 t, ‖exp (s • LinearMap.toContinuousLinearMap L)‖ ≤ 1)
    (hL' : ∀ s ∈ Set.Icc 0 t, ‖exp (s • LinearMap.toContinuousLinearMap L')‖ ≤ 1) :
    ‖(LinearMap.toContinuousLinearMap R).comp (exp (t • LinearMap.toContinuousLinearMap L)) -
        (exp (t • LinearMap.toContinuousLinearMap L')).comp (LinearMap.toContinuousLinearMap R)‖ ≤
      t * ‖LinearMap.toContinuousLinearMap (R ∘ₗ L - L' ∘ₗ R)‖ :=
  fd_norm_sub_le_of_contraction R L L' ht hL hL'

end Matrices

end APEX.Unified.Duhamel

