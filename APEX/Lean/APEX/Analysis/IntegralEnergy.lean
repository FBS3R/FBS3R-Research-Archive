import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.L2Space
import APEX.Analysis.ForcedEnergy

/-!
# A priori bounds for forced dissipative systems: integral (mild / AC) formulation, `L¹` forcing

`E` is a real inner product space, complete (a Hilbert space; e.g. any finite-dimensional one).
`A Q : E → E` are **arbitrary maps** (no linearity, continuity or measurability) with
`⟪Q y, y⟫ = 0` and `λ‖y‖² ≤ ⟪A y, y⟫` (`λ ≥ 0`; `λ = 0` is the non-coercive case), `ν ≥ 0`.

**Solution concept (integral / absolutely continuous form).** On `[0,T]`:
`x t = x 0 + ∫₀ᵗ v s ds` for all `t ∈ [0,T]`, with `v` interval-integrable on `[0,T]`, and
`v s = -ν A(x s) - Q(x s) + F s` for a.e. `s ∈ [0,T]`; `F` is only interval-integrable.
(Continuity of `x` is not assumed; it follows from the integral equation.)

Main results:
* `norm_le_forced_integral`: `‖x T‖ ≤ ‖x 0‖ + ∫₀ᵀ ‖F s‖ ds` (under `⟪A y,y⟫ ≥ 0`).
* `norm_le_coercive_integral`: `‖x T‖ ≤ e^{-kT}‖x 0‖ + ∫₀ᵀ e^{-k(T-s)}‖F s‖ ds`, `k = νλ`.
* Abstract versions `exp_norm_le_of_dissipative`, `norm_le_of_dissipative`, which only use the
  a.e. inequality `⟪x s, v s⟫ ≤ -k‖x s‖² + ‖x s‖‖F s‖`, and the core
  `weighted_energy_ineq`: `e^{kT}√(‖x T‖²+ε²) - √(‖x 0‖²+ε²) ≤ ∫₀ᵀ e^{ks}(‖F s‖+kε) ds`.
* Non-blow-up on `[0,T)`, `T < ∞`: `norm_bound_of_local_solution` (classical `HasDerivAt`
  solutions, `F` continuous on `[0,T)` and integrable on `[0,T]`; uses `ForcedEnergy`) and
  `norm_bound_of_local_integral_solution` (integral form): `‖x t‖ ≤ ‖x 0‖ + ∫₀ᵀ‖F‖` for all
  `t ∈ [0,T)`; `no_blowup`, `no_blowup_integral`: the norm is bounded on `[0,T)` (`BddAbove`) and
  does not tend to `+∞` as `t → T⁻`.

**Method.** No FTC for absolutely continuous functions is used (not available in the built
Mathlib). For `g(y) = √(‖y‖²+ε²)` (convex, gradient `y/g(y)`) one has the supporting-hyperplane
inequality `g(y) - g(w) ≤ ⟪y/g(y), y - w⟫`; combined with `x z - x t = ∫ₜᶻ v`, continuity of
`r ↦ e^{kr} x r / g(x r)` and an `η`-slack, this gives a right Dini-derivative bound for
`Φ(t) = e^{kt} g(x t) - ∫₀ᵗ (e^{ks}(‖F‖+kε) + η‖v‖ + η)` at **every** point of `[0,T)`, so
`Φ` is non-increasing (`image_le_of_liminf_slope_right_le_deriv_boundary`); then `η, ε → 0`.

**Not proved here:** existence of (local or global) solutions (Picard–Lindelöf is not in the
built Mathlib), uniqueness, and anything about PDEs. This is an ODE estimate in a finite-dimensional or abstract Hilbert space
(an energy estimate, e.g. for Galerkin truncations); it is **not** a Navier–Stokes regularity result
in `ℝ³`.
-/

open Real intervalIntegral MeasureTheory Set Filter Topology

namespace APEX.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Convexity (supporting-hyperplane) inequality for `g(y) = √(‖y‖² + ε²)`:
`g y - g w ≤ ⟪∇g(y), y - w⟫` with `∇g(y) = y / g(y)`. -/
lemma sqrt_normsq_sub_le (y w : E) {ε : ℝ} (hε : 0 < ε) :
    √(‖y‖ ^ 2 + ε ^ 2) - √(‖w‖ ^ 2 + ε ^ 2)
      ≤ (√(‖y‖ ^ 2 + ε ^ 2))⁻¹ * inner ℝ y (y - w) := by
  set S := √(‖y‖ ^ 2 + ε ^ 2)
  set R := √(‖w‖ ^ 2 + ε ^ 2)
  have hS : 0 < S := sqrt_pos.2 (by positivity)
  have hSsq : S ^ 2 = ‖y‖ ^ 2 + ε ^ 2 := sq_sqrt (by positivity)
  have hRS : ‖y‖ * ‖w‖ + ε ^ 2 ≤ S * R := by
    rw [← sqrt_mul (by positivity)]
    apply le_sqrt_of_sq_le
    nlinarith [sq_nonneg (‖y‖ - ‖w‖), sq_nonneg ε]
  have hin : inner ℝ y w ≤ ‖y‖ * ‖w‖ := real_inner_le_norm y w
  rw [inv_mul_eq_div, le_div_iff₀ hS, inner_sub_right, real_inner_self_eq_norm_sq]
  nlinarith

/-- Pointwise dissipation estimate in regularised form. -/
lemma reg_dissip {k ε S nx f I : ℝ} (hk : 0 ≤ k) (hε : 0 < ε) (hf : 0 ≤ f)
    (hS : 0 < S) (hSsq : S ^ 2 = nx ^ 2 + ε ^ 2) (hnx : 0 ≤ nx)
    (hI : I ≤ -k * nx ^ 2 + nx * f) :
    k * S + S⁻¹ * I ≤ f + k * ε := by
  have hxS : nx ≤ S := by nlinarith [sq_nonneg ε]
  have hεS : ε ≤ S := by nlinarith [sq_nonneg nx]
  have : S⁻¹ * I ≤ f + k * ε - k * S := by
    rw [inv_mul_eq_div, div_le_iff₀ hS]
    nlinarith [mul_nonneg hf (sub_nonneg.2 hxS), mul_nonneg hk (mul_nonneg hε.le (sub_nonneg.2 hεS))]
  linarith

/-- **Core weighted energy inequality (integral formulation).**
`x t = x 0 + ∫₀ᵗ v` on `[0,T]`, `v` and `F` interval integrable, and a.e. on `[0,T]`
`⟪x, v⟫ ≤ -k‖x‖² + ‖x‖‖F‖`. Then for every `ε > 0`
`e^{kT} √(‖x T‖²+ε²) - √(‖x 0‖²+ε²) ≤ ∫₀ᵀ e^{ks} (‖F s‖ + kε) ds`. -/
theorem weighted_energy_ineq {x v F : ℝ → E} {T k ε : ℝ} (hT : 0 ≤ T) (hk : 0 ≤ k)
    (hε : 0 < ε) (hv : IntervalIntegrable v volume 0 T) (hF : IntervalIntegrable F volume 0 T)
    (hxint : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0)..t, v s)
    (hdiss : ∀ᵐ s, s ∈ Icc 0 T → inner ℝ (x s) (v s) ≤ -k * ‖x s‖ ^ 2 + ‖x s‖ * ‖F s‖) :
    exp (k * T) * √(‖x T‖ ^ 2 + ε ^ 2) - √(‖x 0‖ ^ 2 + ε ^ 2)
      ≤ ∫ s in (0)..T, exp (k * s) * (‖F s‖ + k * ε) := by
  have hsub : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, uIcc a b ⊆ uIcc 0 T := fun a ha b hb =>
    uIcc_subset_uIcc (by rwa [uIcc_of_le hT]) (by rwa [uIcc_of_le hT])
  have hvi : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, IntervalIntegrable v volume a b :=
    fun a ha b hb => hv.mono_set (hsub a ha b hb)
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  -- continuity of `x`
  have hxc : ContinuousOn x (Icc 0 T) := by
    have h1 := continuousOn_primitive_interval' hv (left_mem_uIcc (a := (0:ℝ)) (b := T))
    rw [uIcc_of_le hT] at h1
    exact (continuousOn_const.add h1).congr fun t ht => hxint t ht
  set g : ℝ → ℝ := fun t => √(‖x t‖ ^ 2 + ε ^ 2) with hg_def
  have hgc : ContinuousOn g (Icc 0 T) := ((hxc.norm.pow 2).add continuousOn_const).sqrt
  have hgpos : ∀ t, 0 < g t := fun t => sqrt_pos.2 (by positivity)
  have hexpc : Continuous fun r : ℝ => exp (k * r) := by fun_prop
  set W : ℝ → E := fun r => exp (k * r) • ((g r)⁻¹ • x r) with hW_def
  have hWc : ContinuousOn W (Icc 0 T) :=
    hexpc.continuousOn.smul ((hgc.inv₀ fun t _ => (hgpos t).ne').smul hxc)
  have hexpint : ∀ a b : ℝ, ∫ r in a..b, exp (k * r) * k = exp (k * b) - exp (k * a) := by
    intro a b
    refine integral_eq_sub_of_hasDerivAt (f := fun r => exp (k * r)) (fun r _ => ?_)
      ((by fun_prop : Continuous fun r : ℝ => exp (k * r) * k).intervalIntegrable _ _)
    simpa using ((hasDerivAt_id r).const_mul k).exp
  have key : ∀ η > 0, exp (k * T) * g T - g 0 ≤ (∫ s in (0)..T, exp (k * s) * (‖F s‖ + k * ε))
      + η * (∫ s in (0)..T, ‖v s‖) + η * T := by
    intro η hη
    set h : ℝ → ℝ := fun s => exp (k * s) * (‖F s‖ + k * ε) + η * ‖v s‖ + η with hh_def
    have hA : IntervalIntegrable (fun s => exp (k * s) * (‖F s‖ + k * ε)) volume 0 T :=
      (hF.norm.add intervalIntegrable_const).continuousOn_mul hexpc.continuousOn
    have h0T : IntervalIntegrable h volume 0 T :=
      (hA.add (hv.norm.const_mul η)).add intervalIntegrable_const
    have hhi : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, IntervalIntegrable h volume a b :=
      fun a ha b hb => h0T.mono_set (hsub a ha b hb)
    set Φ : ℝ → ℝ := fun t => exp (k * t) * g t - ∫ s in (0)..t, h s with hΦ_def
    have hΦc : ContinuousOn Φ (Icc 0 T) := by
      have h1 := continuousOn_primitive_interval' h0T (left_mem_uIcc (a := (0:ℝ)) (b := T))
      rw [uIcc_of_le hT] at h1
      exact (hexpc.continuousOn.mul hgc).sub h1
    have hloc : ∀ t₀ ∈ Ico 0 T, ∀ᶠ z in 𝓝[>] t₀, Φ z ≤ Φ t₀ := by
      intro t₀ ht₀
      have ht₀I : t₀ ∈ Icc 0 T := Ico_subset_Icc_self ht₀
      obtain ⟨δ₁, hδ₁, H1⟩ :=
        Metric.continuousWithinAt_iff.1 (hWc t₀ ht₀I) (η / 2) (half_pos hη)
      set q : ℝ → ℝ := fun r => k * exp (k * r) * (g t₀ - g r) with hq_def
      have hqc : ContinuousOn q (Icc 0 T) :=
        (continuousOn_const.mul hexpc.continuousOn).mul (continuousOn_const.sub hgc)
      obtain ⟨δ₂, hδ₂, H2⟩ := Metric.continuousWithinAt_iff.1 (hqc t₀ ht₀I) η hη
      have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
      filter_upwards [Ioo_mem_nhdsGT (lt_min ht₀.2 (by linarith : t₀ < t₀ + min δ₁ δ₂))]
        with z hz
      obtain ⟨hz1, hz2⟩ := hz
      have hzT : z ≤ T := (hz2.trans_le (min_le_left _ _)).le
      have hzδ : z < t₀ + min δ₁ δ₂ := hz2.trans_le (min_le_right _ _)
      have hzI : z ∈ Icc 0 T := ⟨ht₀.1.trans hz1.le, hzT⟩
      have hrr : ∀ r ∈ Icc t₀ z, r ∈ Icc 0 T ∧ dist r t₀ < δ₁ ∧ dist r t₀ < δ₂ := by
        intro r hr
        refine ⟨⟨ht₀.1.trans hr.1, hr.2.trans hzT⟩, ?_, ?_⟩ <;>
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hr.1])] <;>
          linarith [min_le_left δ₁ δ₂, min_le_right δ₁ δ₂, hr.2]
      have hsplit : (∫ s in (0)..z, h s) - ∫ s in (0)..t₀, h s = ∫ s in t₀..z, h s :=
        integral_interval_sub_left (hhi 0 h0 z hzI) (hhi 0 h0 t₀ ht₀I)
      have hvsub : x z - x t₀ = ∫ s in t₀..z, v s := by
        rw [hxint z hzI, hxint t₀ ht₀I, add_sub_add_left_eq_sub,
          integral_interval_sub_left (hvi 0 h0 z hzI) (hvi 0 h0 t₀ ht₀I)]
      have hconv := sqrt_normsq_sub_le (x z) (x t₀) hε
      have step1 : exp (k * z) * g z - exp (k * t₀) * g t₀
          ≤ inner ℝ (W z) (x z - x t₀) + (exp (k * z) - exp (k * t₀)) * g t₀ := by
        have : inner ℝ (W z) (x z - x t₀)
            = exp (k * z) * ((g z)⁻¹ * inner ℝ (x z) (x z - x t₀)) := by
          simp only [hW_def, real_inner_smul_left]
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_left hconv (exp_pos (k * z)).le]
      have hvtz := hvi t₀ ht₀I z hzI
      have hinnI : IntervalIntegrable (fun r => inner ℝ (W z) (v r)) volume t₀ z :=
        ⟨hvtz.1.const_inner _, hvtz.2.const_inner _⟩
      have hexI : IntervalIntegrable (fun r => exp (k * r) * k * g t₀) volume t₀ z :=
        (by fun_prop : Continuous fun r : ℝ => exp (k * r) * k * g t₀).intervalIntegrable _ _
      have step2 : inner ℝ (W z) (x z - x t₀) + (exp (k * z) - exp (k * t₀)) * g t₀
          = ∫ r in t₀..z, (inner ℝ (W z) (v r) + exp (k * r) * k * g t₀) := by
        rw [integral_add hinnI hexI, hvsub, ← hexpint,
          intervalIntegral.integral_mul_const (g t₀) (fun r => exp (k * r) * k)]
        congr 1
        have := (innerSL ℝ (W z)).intervalIntegral_comp_comm hvtz
        simpa only [innerSL_apply_apply] using this.symm
      have step3 : ∫ r in t₀..z, (inner ℝ (W z) (v r) + exp (k * r) * k * g t₀)
          ≤ ∫ r in t₀..z, h r := by
        refine integral_mono_ae_restrict hz1.le (hinnI.add hexI) (hhi t₀ ht₀I z hzI) ?_
        have hm : ∀ᵐ r ∂(volume.restrict (Icc t₀ z)), r ∈ Icc t₀ z :=
          ae_restrict_mem measurableSet_Icc
        filter_upwards [hm, ae_restrict_of_ae hdiss] with r hr hdr
        obtain ⟨hr0T, hr1, hr2⟩ := hrr r hr
        have hd := hdr hr0T
        obtain ⟨_, hz1', _⟩ := hrr z (right_mem_Icc.2 hz1.le)
        have hWzr : ‖W z - W r‖ ≤ η := by
          have a := H1 hr0T hr1
          have b := H1 hzI hz1'
          rw [dist_eq_norm] at a b
          calc ‖W z - W r‖ = ‖(W z - W t₀) - (W r - W t₀)‖ := by congr 1; abel
            _ ≤ ‖W z - W t₀‖ + ‖W r - W t₀‖ := norm_sub_le _ _
            _ ≤ η := by linarith
        have hq : k * exp (k * r) * (g t₀ - g r) ≤ η := by
          have := H2 hr0T hr2
          have hq0 : q t₀ = 0 := by simp [hq_def]
          rw [Real.dist_eq, hq0, sub_zero] at this
          exact (le_abs_self _).trans this.le
        have hinner1 : inner ℝ (W z) (v r) ≤ inner ℝ (W r) (v r) + η * ‖v r‖ := by
          have e : inner ℝ (W z) (v r) = inner ℝ (W r) (v r) + inner ℝ (W z - W r) (v r) := by
            rw [inner_sub_left]; ring
          rw [e]
          have := real_inner_le_norm (W z - W r) (v r)
          nlinarith [norm_nonneg (v r)]
        have hWr : inner ℝ (W r) (v r) = exp (k * r) * ((g r)⁻¹ * inner ℝ (x r) (v r)) := by
          simp only [hW_def, real_inner_smul_left]
        have hm := reg_dissip hk hε (norm_nonneg (F r)) (hgpos r)
          (sq_sqrt (by positivity)) (norm_nonneg (x r)) hd
        have he := exp_pos (k * r)
        simp only [hh_def]
        nlinarith [mul_le_mul_of_nonneg_left hm he.le]
      simp only [hΦ_def]
      linarith [step1, step2, step3, hsplit]
    have hmono := image_le_of_liminf_slope_right_le_deriv_boundary hΦc
      (B := fun _ => Φ 0) (B' := fun _ => 0) le_rfl continuousOn_const
      (fun _ _ => hasDerivWithinAt_const _ _ _)
      (fun t ht r hr => by
        refine (((hloc t ht).and self_mem_nhdsWithin).mono fun z ⟨hz, hzt⟩ => ?_).frequently
        rw [slope_def_field]
        exact (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [show t < z from hzt])).trans_lt hr)
      (right_mem_Icc.2 hT)
    simp only [hΦ_def, mul_zero, exp_zero, one_mul, integral_same, sub_zero] at hmono
    have hsplitT : ∫ s in (0)..T, h s = (∫ s in (0)..T, exp (k * s) * (‖F s‖ + k * ε))
        + η * (∫ s in (0)..T, ‖v s‖) + η * T := by
      simp only [hh_def]
      rw [integral_add (hA.add (hv.norm.const_mul η)) intervalIntegrable_const,
        integral_add hA (hv.norm.const_mul η), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]; ring
    linarith
  -- let η → 0
  by_contra hcon
  push Not at hcon
  set D := exp (k * T) * g T - g 0 - ∫ s in (0)..T, exp (k * s) * (‖F s‖ + k * ε)
  have hDdef : D = exp (k * T) * g T - g 0 - ∫ s in (0)..T, exp (k * s) * (‖F s‖ + k * ε) := rfl
  have hD : 0 < D := by simp only [D, hg_def]; linarith
  have hN : 0 ≤ ∫ s in (0)..T, ‖v s‖ := integral_nonneg hT fun s _ => norm_nonneg _
  have := key (D / (2 * ((∫ s in (0)..T, ‖v s‖) + T + 1))) (by positivity)
  set N := ∫ s in (0)..T, ‖v s‖
  have hpos : 0 < 2 * (N + T + 1) := by positivity
  have hc : D / (2 * (N + T + 1)) * (N + T + 1) = D / 2 := by field_simp
  have hc0 : 0 < D / (2 * (N + T + 1)) := div_pos hD hpos
  have e : D / (2 * (N + T + 1)) * N + D / (2 * (N + T + 1)) * T ≤ D / 2 := by
    nlinarith
  linarith

/-- **Exponentially weighted a priori bound, abstract integral form.**
Under the hypotheses of `weighted_energy_ineq` (no `ε`):
`e^{kT} ‖x T‖ ≤ ‖x 0‖ + ∫₀ᵀ e^{ks} ‖F s‖ ds`. -/
theorem exp_norm_le_of_dissipative {x v F : ℝ → E} {T k : ℝ} (hT : 0 ≤ T) (hk : 0 ≤ k)
    (hv : IntervalIntegrable v volume 0 T) (hF : IntervalIntegrable F volume 0 T)
    (hxint : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0)..t, v s)
    (hdiss : ∀ᵐ s, s ∈ Icc 0 T → inner ℝ (x s) (v s) ≤ -k * ‖x s‖ ^ 2 + ‖x s‖ * ‖F s‖) :
    exp (k * T) * ‖x T‖ ≤ ‖x 0‖ + ∫ s in (0)..T, exp (k * s) * ‖F s‖ := by
  have hexpc : Continuous fun r : ℝ => exp (k * r) := by fun_prop
  have hexpint : ∫ r in (0)..T, exp (k * r) * k = exp (k * T) - 1 := by
    rw [integral_eq_sub_of_hasDerivAt (f := fun r => exp (k * r)) (fun r _ => by
      simpa using ((hasDerivAt_id r).const_mul k).exp)
      ((by fun_prop : Continuous fun r : ℝ => exp (k * r) * k).intervalIntegrable _ _)]
    simp
  have hI : IntervalIntegrable (fun s => exp (k * s) * ‖F s‖) volume 0 T :=
    hF.norm.continuousOn_mul hexpc.continuousOn
  set I := ∫ s in (0)..T, exp (k * s) * ‖F s‖ with hI_def
  have he := exp_pos (k * T)
  have key : ∀ ε > 0, exp (k * T) * ‖x T‖ ≤ ‖x 0‖ + I + ε * exp (k * T) := by
    intro ε hε
    have h := weighted_energy_ineq hT hk hε hv hF hxint hdiss
    have hsplit : ∫ s in (0)..T, exp (k * s) * (‖F s‖ + k * ε) = I + (exp (k * T) - 1) * ε := by
      have : ∀ s, exp (k * s) * (‖F s‖ + k * ε) = exp (k * s) * ‖F s‖ + exp (k * s) * k * ε :=
        fun s => by ring
      simp_rw [this]
      rw [integral_add hI ((by fun_prop : Continuous fun r : ℝ => exp (k * r) * k * ε).intervalIntegrable _ _),
        intervalIntegral.integral_mul_const ε (fun r => exp (k * r) * k), hexpint]
    rw [hsplit] at h
    have hy0 : √(‖x 0‖ ^ 2 + ε ^ 2) ≤ ‖x 0‖ + ε :=
      (sqrt_le_left (by positivity)).2 (by nlinarith [norm_nonneg (x 0)])
    have hyT : ‖x T‖ ≤ √(‖x T‖ ^ 2 + ε ^ 2) :=
      (le_sqrt (norm_nonneg _) (by positivity)).2 (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left hyT he.le]
  by_contra hcon
  push Not at hcon
  have := key ((exp (k * T) * ‖x T‖ - (‖x 0‖ + I)) / (2 * exp (k * T)))
    (div_pos (by linarith) (by positivity))
  have e : (exp (k * T) * ‖x T‖ - (‖x 0‖ + I)) / (2 * exp (k * T)) * exp (k * T)
      = (exp (k * T) * ‖x T‖ - (‖x 0‖ + I)) / 2 := by field_simp
  linarith

/-- **Coercive a priori bound, abstract integral form (convolution form).**
`‖x T‖ ≤ e^{-kT} ‖x 0‖ + ∫₀ᵀ e^{-k(T-s)} ‖F s‖ ds`. -/
theorem norm_le_of_dissipative {x v F : ℝ → E} {T k : ℝ} (hT : 0 ≤ T) (hk : 0 ≤ k)
    (hv : IntervalIntegrable v volume 0 T) (hF : IntervalIntegrable F volume 0 T)
    (hxint : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0)..t, v s)
    (hdiss : ∀ᵐ s, s ∈ Icc 0 T → inner ℝ (x s) (v s) ≤ -k * ‖x s‖ ^ 2 + ‖x s‖ * ‖F s‖) :
    ‖x T‖ ≤ exp (-k * T) * ‖x 0‖ + ∫ s in (0)..T, exp (-k * (T - s)) * ‖F s‖ := by
  have h := exp_norm_le_of_dissipative hT hk hv hF hxint hdiss
  have h2 := mul_le_mul_of_nonneg_left h (exp_pos (-k * T)).le
  have e1 : exp (-k * T) * (exp (k * T) * ‖x T‖) = ‖x T‖ := by
    rw [← mul_assoc, ← exp_add]; simp
  have e2 : exp (-k * T) * (‖x 0‖ + ∫ s in (0)..T, exp (k * s) * ‖F s‖)
      = exp (-k * T) * ‖x 0‖ + ∫ s in (0)..T, exp (-k * (T - s)) * ‖F s‖ := by
    have hi : ∫ s in (0)..T, exp (-k * T) * (exp (k * s) * ‖F s‖)
        = ∫ s in (0)..T, exp (-k * (T - s)) * ‖F s‖ :=
      intervalIntegral.integral_congr fun s _ => by
        rw [← mul_assoc, ← exp_add, show -k * T + k * s = -k * (T - s) by ring]
    rw [mul_add, ← intervalIntegral.integral_const_mul, hi]
  rw [e1, e2] at h2
  exact h2

omit [CompleteSpace E] in
/-- The ODE `v = -ν A x - Q x + F` (a.e.) with `⟪Q y,y⟫ = 0`, `λ‖y‖² ≤ ⟪A y,y⟫` gives the
pointwise dissipation inequality with `k = νλ`. -/
lemma dissip_of_ode {x v F : ℝ → E} (A Q : E → E) {ν lam T : ℝ} (hν : 0 ≤ ν)
    (hA : ∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A y) y) (hQ : ∀ y, inner ℝ (Q y) y = 0)
    (hode : ∀ᵐ s, s ∈ Icc 0 T → v s = -(ν • A (x s)) - Q (x s) + F s) :
    ∀ᵐ s, s ∈ Icc 0 T →
      inner ℝ (x s) (v s) ≤ -(ν * lam) * ‖x s‖ ^ 2 + ‖x s‖ * ‖F s‖ := by
  filter_upwards [hode] with s hs hsI
  rw [hs hsI, inner_add_right, inner_sub_right, inner_neg_right, real_inner_smul_right,
    real_inner_comm (Q (x s)), hQ]
  have h1 := hA (x s)
  have h2 := real_inner_le_norm (x s) (F s)
  rw [real_inner_comm] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hν
  nlinarith

/-- **Coercive bound, integral (absolutely continuous / mild) formulation, `L¹` forcing.**
`x t = x 0 + ∫₀ᵗ v` on `[0,T]`, `v` integrable on `[0,T]`, `v = -νA x - Q x + F` a.e. on `[0,T]`,
`F` interval integrable; `A`, `Q : E → E` arbitrary maps (no continuity/measurability needed)
with `⟪Q y,y⟫ = 0` and `λ‖y‖² ≤ ⟪A y,y⟫`. Then with `k = νλ`:
`‖x T‖ ≤ e^{-kT}‖x 0‖ + ∫₀ᵀ e^{-k(T-s)} ‖F s‖ ds`. -/
theorem norm_le_coercive_integral (x v F : ℝ → E) (A Q : E → E) {ν lam T : ℝ}
    (hν : 0 ≤ ν) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (hA : ∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A y) y) (hQ : ∀ y, inner ℝ (Q y) y = 0)
    (hF : IntervalIntegrable F volume 0 T) (hv : IntervalIntegrable v volume 0 T)
    (hxint : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0)..t, v s)
    (hode : ∀ᵐ s, s ∈ Icc 0 T → v s = -(ν • A (x s)) - Q (x s) + F s) :
    ‖x T‖ ≤ exp (-(ν * lam) * T) * ‖x 0‖
      + ∫ s in (0)..T, exp (-(ν * lam) * (T - s)) * ‖F s‖ :=
  norm_le_of_dissipative hT (mul_nonneg hν hlam) hv hF hxint (dissip_of_ode A Q hν hA hQ hode)

/-- **Main bound, integral formulation, `L¹` forcing:** `‖x T‖ ≤ ‖x 0‖ + ∫₀ᵀ ‖F s‖ ds`
under `0 ≤ ⟪A y,y⟫`, `⟪Q y,y⟫ = 0`. -/
theorem norm_le_forced_integral (x v F : ℝ → E) (A Q : E → E) {ν T : ℝ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hA : ∀ y, 0 ≤ inner ℝ (A y) y) (hQ : ∀ y, inner ℝ (Q y) y = 0)
    (hF : IntervalIntegrable F volume 0 T) (hv : IntervalIntegrable v volume 0 T)
    (hxint : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0)..t, v s)
    (hode : ∀ᵐ s, s ∈ Icc 0 T → v s = -(ν • A (x s)) - Q (x s) + F s) :
    ‖x T‖ ≤ ‖x 0‖ + ∫ s in (0)..T, ‖F s‖ := by
  have h := norm_le_coercive_integral (lam := 0) x v F A Q hν le_rfl hT
    (fun y => by simpa using hA y) hQ hF hv hxint hode
  simpa using h

/-! ### Global continuation: no finite-time blow-up -/

/-- **Non-blow-up, integral formulation.** If on `[0,T)` the function `x` satisfies
`x t = x 0 + ∫₀ᵗ v` with `v` integrable on every `[0,t]`, `t < T`, the ODE a.e. on `[0,T)`, and
`F` is integrable on `[0,T]`, then `‖x t‖ ≤ ‖x 0‖ + ∫₀ᵀ ‖F‖` for all `t ∈ [0,T)`. -/
theorem norm_bound_of_local_integral_solution (x v F : ℝ → E) (A Q : E → E) {ν T : ℝ}
    (hν : 0 ≤ ν) (hA : ∀ y, 0 ≤ inner ℝ (A y) y) (hQ : ∀ y, inner ℝ (Q y) y = 0)
    (hF : IntervalIntegrable F volume 0 T)
    (hv : ∀ t ∈ Ico 0 T, IntervalIntegrable v volume 0 t)
    (hxint : ∀ t ∈ Ico 0 T, x t = x 0 + ∫ s in (0)..t, v s)
    (hode : ∀ᵐ s, s ∈ Ico 0 T → v s = -(ν • A (x s)) - Q (x s) + F s) :
    ∀ t ∈ Ico 0 T, ‖x t‖ ≤ ‖x 0‖ + ∫ s in (0)..T, ‖F s‖ := by
  intro t ht
  have hFt : IntervalIntegrable F volume 0 t :=
    hF.mono_set (uIcc_subset_uIcc left_mem_uIcc
      (by rw [uIcc_of_le (ht.1.trans ht.2.le)]; exact ⟨ht.1, ht.2.le⟩))
  have hsub : ∀ s ∈ Icc 0 t, s ∈ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have h := norm_le_forced_integral x v F A Q hν ht.1 hA hQ hFt (hv t ht)
    (fun s hs => hxint s (hsub s hs))
    (by filter_upwards [hode] with s hs hsI using hs (hsub s hsI))
  have hm := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2.le
    (Eventually.of_forall fun s => norm_nonneg _) hF.norm
  linarith

omit [CompleteSpace E] in
/-- **Non-blow-up, classical formulation.** A classical local solution on `[0,T)`
(`x` continuous on `[0,T)`, `HasDerivAt` with the ODE at every `t ∈ (0,T)`, `F` continuous on
`[0,T)` and integrable on `[0,T]`) satisfies `‖x t‖ ≤ ‖x 0‖ + ∫₀ᵀ ‖F‖` on `[0,T)`.
No regularity of `A`, `Q` is needed for the bound (local Lipschitz is only needed for
existence/uniqueness, which is not proved here). -/
theorem norm_bound_of_local_solution (x F : ℝ → E) (A Q : E → E) {ν T : ℝ}
    (hν : 0 ≤ ν) (hA : ∀ y, 0 ≤ inner ℝ (A y) y) (hQ : ∀ y, inner ℝ (Q y) y = 0)
    (hF : ContinuousOn F (Ico 0 T)) (hFi : IntervalIntegrable F volume 0 T)
    (hxc : ContinuousOn x (Ico 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (-(ν • A (x t)) - Q (x t) + F t) t) :
    ∀ t ∈ Ico 0 T, ‖x t‖ ≤ ‖x 0‖ + ∫ s in (0)..T, ‖F s‖ := by
  intro t ht
  have hsub : Icc 0 t ⊆ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have h := norm_le_forced_local x A Q F hν ht.1 hA hQ (hF.mono hsub) (hxc.mono hsub)
    (fun s hs => hx s ⟨hs.1, hs.2.trans ht.2⟩)
  have hm := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2.le
    (Eventually.of_forall fun s => norm_nonneg _) hFi.norm
  linarith

omit [CompleteSpace E] in
/-- **No finite-time blow-up (classical).** For `T < ∞` the norm of a classical local solution
on `[0,T)` is bounded: `sup_{t<T} ‖x t‖ < ∞` (stated as `BddAbove`), and in particular
`‖x t‖` does not tend to `+∞` as `t → T⁻` (for `0 < T`). -/
theorem no_blowup (x F : ℝ → E) (A Q : E → E) {ν T : ℝ} (hT : 0 < T)
    (hν : 0 ≤ ν) (hA : ∀ y, 0 ≤ inner ℝ (A y) y) (hQ : ∀ y, inner ℝ (Q y) y = 0)
    (hF : ContinuousOn F (Ico 0 T)) (hFi : IntervalIntegrable F volume 0 T)
    (hxc : ContinuousOn x (Ico 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (-(ν • A (x t)) - Q (x t) + F t) t) :
    BddAbove ((fun t => ‖x t‖) '' Ico 0 T) ∧
      ¬ Tendsto (fun t => ‖x t‖) (𝓝[<] T) atTop := by
  have hb := norm_bound_of_local_solution x F A Q hν hA hQ hF hFi hxc hx
  refine ⟨⟨_, by rintro _ ⟨t, ht, rfl⟩; exact hb t ht⟩, fun htend => ?_⟩
  have h1 := htend.eventually (eventually_gt_atTop (‖x 0‖ + ∫ s in (0)..T, ‖F s‖))
  have h2 : Ioo 0 T ∈ 𝓝[<] T := Ioo_mem_nhdsLT hT
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  exact absurd (hb t (Ioo_subset_Ico_self ht2)) (not_le.2 ht1)

/-- **No finite-time blow-up (integral formulation, `L¹` forcing).** -/
theorem no_blowup_integral (x v F : ℝ → E) (A Q : E → E) {ν T : ℝ} (hT : 0 < T)
    (hν : 0 ≤ ν) (hA : ∀ y, 0 ≤ inner ℝ (A y) y) (hQ : ∀ y, inner ℝ (Q y) y = 0)
    (hF : IntervalIntegrable F volume 0 T)
    (hv : ∀ t ∈ Ico 0 T, IntervalIntegrable v volume 0 t)
    (hxint : ∀ t ∈ Ico 0 T, x t = x 0 + ∫ s in (0)..t, v s)
    (hode : ∀ᵐ s, s ∈ Ico 0 T → v s = -(ν • A (x s)) - Q (x s) + F s) :
    BddAbove ((fun t => ‖x t‖) '' Ico 0 T) ∧
      ¬ Tendsto (fun t => ‖x t‖) (𝓝[<] T) atTop := by
  have hb := norm_bound_of_local_integral_solution x v F A Q hν hA hQ hF hv hxint hode
  refine ⟨⟨_, by rintro _ ⟨t, ht, rfl⟩; exact hb t ht⟩, fun htend => ?_⟩
  have h1 := htend.eventually (eventually_gt_atTop (‖x 0‖ + ∫ s in (0)..T, ‖F s‖))
  have h2 : Ioo 0 T ∈ 𝓝[<] T := Ioo_mem_nhdsLT hT
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  exact absurd (hb t (Ioo_subset_Ico_self ht2)) (not_le.2 ht1)

end APEX.Analysis

