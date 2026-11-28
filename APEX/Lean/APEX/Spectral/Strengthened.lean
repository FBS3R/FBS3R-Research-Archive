import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic

/-!
# Strengthened spectral (Källén–Lehmann-type) no-go for nonlocal propagators

**Setting.** `ρ : Measure ℝ` is a positive measure with `ρ (Iio 0) = 0` (support in `[0,∞)`),
possibly **infinite**: finiteness is replaced by `Integrable (fun s => (1+s)⁻¹) ρ`, i.e.
`∫ (1+s)⁻¹ dρ < ∞`. For `x > 0`, `G ρ x = ∫ (x+s)⁻¹ dρ(s)` is then finite since
`(x+s)⁻¹ ≤ (1 + x⁻¹)(1+s)⁻¹` for `s ≥ 0` (`integrable_inv_add`).

**Results.**
1. `monotoneOn_mul_G`: `x ↦ x G(x)` is non-decreasing on `(0,∞)`; `antitoneOn_G`: `G` is
   non-increasing on `(0,∞)`; `G_pos`, `mul_G_pos`: `G(x) > 0` for `x > 0` if `ρ ≠ 0`.
2. `tendsto_ofReal_mul_G`: `ENNReal.ofReal (x G(x)) → ρ(ℝ) = ρ([0,∞))` in `ℝ≥0∞` as `x → ∞`
   (monotone convergence). Corollaries: `tendsto_mul_G_atTop_of_infinite` (`ρ(ℝ) = ∞` ⇒
   `x G(x) → ∞`) and `tendsto_mul_G_of_finite` (`ρ(ℝ) < ∞` ⇒ `x G(x) → ρ(ℝ)` in `ℝ`).
3. `no_representation_of_tendsto_zero`: if `x f(x) → 0` (`f = o(1/x)`), no nonzero such `ρ` has
   `G = f` on `(0,∞)`; `mul_G_ge_of_le`: `x G(x) ≥ x₀ G(x₀) > 0` for `x ≥ x₀ > 0`;
   `no_representation_of_decrease`: if `x f(x)` strictly decreases between two points of
   `(0,∞)`, no such `ρ` (zero allowed) represents `f`; `no_representation_exp_div` for
   `f = exp(-a x)/x`, `a > 0`.
4. `tanh_le_rel_error`: for `0 < x ≤ y` (any real `a`), if `|G(t)/f(t) - 1| ≤ ε` on `[x,y]`
   with `f(t) = exp(-a t)/t`, then `ε ≥ tanh(a(y-x)/2)`. `rel_error_sharp`: for `a ≥ 0` the point
   mass `c δ₀`, `c = 2e^{-ax}e^{-ay}/(e^{-ax}+e^{-ay})`, has relative error `≤ tanh(a(y-x)/2)`
   on `[x,y]`, with equality at both endpoints. Hence the infimum over admissible `ρ` of the
   uniform relative error on `[x,y]` is exactly `tanh(a(y-x)/2)`, and a point mass attains it.
5. Matrix version with finitely many atoms, `ρ = ∑_k δ_{s_k} P_k`, `P_k` PSD over an `RCLike`
   field, `s_k ≥ 0`, `Gmat s P x = ∑_k (x+s_k)⁻¹ P_k`: `loewner_mono_mul_Gmat` (`yG(y) - xG(x)`
   is PSD for `0 < x ≤ y`); `polarisation_is_stieltjes` (`v* G(x) v = G ρ_v x` for the scalar
   measure `ρ_v = ∑_k (v* P_k v) δ_{s_k}`, which satisfies the scalar hypotheses);
   `matrix_no_representation_exp_div` and `matrix_tanh_le_rel_error` (per polarisation).

**Physical scope.** These are *necessary conditions* of Källén–Lehmann type: a propagator that
is a positive superposition of free massive (or massless) propagators `1/(x+s)` — `x` playing the
role of the Euclidean momentum squared `-□`, `s` of the squared mass — must have `x G(x)`
non-decreasing and bounded below at large `x`. Nonlocal propagators of the type
`e^{-a□}/□`, i.e. `exp(-a x)/x`, violate this, and the `tanh` bound quantifies how badly *any*
positive spectral superposition must fail to approximate them on a finite window `[x,y]`.
Nothing here proves or disproves the existence or consistency of any theory of quantum gravity;
it shows only that such propagators are **not** positive spectral superpositions (in the sense
above, with scalar or finitely-atomic PSD-matrix-valued spectral measures).
General (non-atomic) PSD-matrix-valued spectral measures are not treated.
-/

open MeasureTheory Filter Topology Set

namespace APEX.Spectral.Strong

/-- Stieltjes-type transform `G(x) = ∫ (x+s)⁻¹ dρ(s)`. -/
noncomputable def G (ρ : Measure ℝ) (x : ℝ) : ℝ := ∫ s, (x + s)⁻¹ ∂ρ

variable {ρ : Measure ℝ}

lemma ae_nonneg (hsupp : ρ (Iio 0) = 0) : ∀ᵐ s ∂ρ, 0 ≤ s := by
  rw [ae_iff]; convert hsupp using 2; ext s; simp

/-- `(x+s)⁻¹ ≤ (1 + x⁻¹) (1+s)⁻¹` for `x > 0`, `s ≥ 0`. -/
lemma inv_add_le {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    (x + s)⁻¹ ≤ (1 + x⁻¹) * (1 + s)⁻¹ := by
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith), one_mul]
  have : (1 + x⁻¹) * (x + s) = x + s + 1 + s * x⁻¹ := by field_simp; ring
  rw [this]; have : 0 ≤ s * x⁻¹ := by positivity
  linarith

lemma integrable_inv_add (hsupp : ρ (Iio 0) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ)
    {x : ℝ} (hx : 0 < x) : Integrable (fun s => (x + s)⁻¹) ρ := by
  refine Integrable.mono' (hint.const_mul (1 + x⁻¹)) ?_ ?_
  · exact (measurable_const.add measurable_id).inv.aestronglyMeasurable
  · filter_upwards [ae_nonneg hsupp] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by linarith))]
    exact inv_add_le hx hs

lemma integrable_div_add (hsupp : ρ (Iio 0) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ)
    {x : ℝ} (hx : 0 < x) : Integrable (fun s => x / (x + s)) ρ := by
  simpa [div_eq_mul_inv] using (integrable_inv_add hsupp hint hx).const_mul x

lemma mul_G_eq (x : ℝ) : x * G ρ x = ∫ s, x / (x + s) ∂ρ := by
  rw [G, ← integral_const_mul]; rfl

/-! ### 1. Monotonicity and positivity -/

/-- **Monotonicity.** `x ↦ x·G(x)` is non-decreasing on `(0,∞)`. -/
theorem monotoneOn_mul_G (hsupp : ρ (Iio 0) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ) :
    MonotoneOn (fun x => x * G ρ x) (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  simp only [mul_G_eq]
  refine integral_mono_ae (integrable_div_add hsupp hint hx) (integrable_div_add hsupp hint hy) ?_
  filter_upwards [ae_nonneg hsupp] with s hs
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `G` is non-increasing on `(0,∞)`. -/
theorem antitoneOn_G (hsupp : ρ (Iio 0) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ) :
    AntitoneOn (G ρ) (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  refine integral_mono_ae (integrable_inv_add hsupp hint hy) (integrable_inv_add hsupp hint hx) ?_
  filter_upwards [ae_nonneg hsupp] with s hs
  exact inv_anti₀ (by linarith) (by linarith)

lemma G_nonneg (hsupp : ρ (Iio 0) = 0) (_hint : Integrable (fun s => (1 + s)⁻¹) ρ)
    {x : ℝ} (hx : 0 < x) : 0 ≤ G ρ x := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_nonneg hsupp] with s hs
  exact inv_nonneg.2 (by linarith)

/-- `G(x) > 0` for `x > 0` when `ρ ≠ 0`. -/
theorem G_pos (hsupp : ρ (Iio 0) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ) (hρ : ρ ≠ 0)
    {x : ℝ} (hx : 0 < x) : 0 < G ρ x := by
  have hnn : 0 ≤ᵐ[ρ] fun s => (x + s)⁻¹ := by
    filter_upwards [ae_nonneg hsupp] with s hs
    exact inv_nonneg.2 (by linarith)
  rw [G, integral_pos_iff_support_of_nonneg_ae hnn (integrable_inv_add hsupp hint hx)]
  have hsub : (Function.support fun s : ℝ => (x + s)⁻¹)ᶜ ⊆ Iio 0 := by
    intro s hs
    simp only [mem_compl_iff, Function.mem_support, ne_eq, not_not, inv_eq_zero] at hs
    simp only [mem_Iio]; linarith
  have hc : ρ (Function.support fun s : ℝ => (x + s)⁻¹)ᶜ = 0 :=
    le_antisymm ((measure_mono hsub).trans hsupp.le) bot_le
  have hu : ρ univ ≠ 0 := by rwa [Ne, Measure.measure_univ_eq_zero]
  refine pos_iff_ne_zero.2 fun h0 => hu ?_
  rw [← union_compl_self (Function.support fun s : ℝ => (x + s)⁻¹)]
  exact le_antisymm ((measure_union_le _ _).trans (by rw [h0, hc, add_zero])) bot_le

theorem mul_G_pos (hsupp : ρ (Iio 0) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ)
    (hρ : ρ ≠ 0) {x : ℝ} (hx : 0 < x) : 0 < x * G ρ x :=
  mul_pos hx (G_pos hsupp hint hρ hx)

/-! ### 2. The limit `x G(x) → ρ([0,∞))` in `ℝ≥0∞` -/

lemma tendsto_div_add (M : ℝ) : Tendsto (fun x : ℝ => x / (x + M)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun x : ℝ => M / (x + M)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
  have : Tendsto (fun x : ℝ => 1 - M / (x + M)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h0
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (-M)] with x hx
  have hne : x + M ≠ 0 := by linarith
  rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]; ring

lemma ofReal_mul_G_eq (hsupp : ρ (Iio 0) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ)
    {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (x * G ρ x) = ∫⁻ s, ENNReal.ofReal (x / (x + s)) ∂ρ := by
  rw [mul_G_eq, ofReal_integral_eq_lintegral_ofReal (integrable_div_add hsupp hint hx)]
  filter_upwards [ae_nonneg hsupp] with s hs
  positivity

/-- **Limit in the extended sense.** `x·G(x) → ρ(ℝ) = ρ([0,∞))` in `ℝ≥0∞` as `x → ∞`
(monotone convergence for `∫⁻ ofReal (x/(x+s)) dρ`); `ρ` may be infinite. -/
theorem tendsto_ofReal_mul_G (hsupp : ρ (Iio 0) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ) :
    Tendsto (fun x => ENNReal.ofReal (x * G ρ x)) atTop (𝓝 (ρ univ)) := by
  -- along the integers `n+1`
  have hseq : Tendsto (fun n : ℕ => ∫⁻ s, ENNReal.ofReal (((n : ℝ) + 1) / (((n : ℝ) + 1) + s)) ∂ρ)
      atTop (𝓝 (∫⁻ _, 1 ∂ρ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) ?_ ?_
    · exact (measurable_const.div (measurable_const.add measurable_id)).ennreal_ofReal.aemeasurable
    · filter_upwards [ae_nonneg hsupp] with s hs
      intro m n hmn
      refine ENNReal.ofReal_le_ofReal ?_
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · filter_upwards with s
      rw [← ENNReal.ofReal_one]
      refine ENNReal.tendsto_ofReal ((tendsto_div_add s).comp ?_)
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  rw [lintegral_one] at hseq
  have hseq' : Tendsto (fun n : ℕ => ENNReal.ofReal (((n : ℝ) + 1) * G ρ ((n : ℝ) + 1)))
      atTop (𝓝 (ρ univ)) :=
    hseq.congr fun n => (ofReal_mul_G_eq hsupp hint (by positivity)).symm
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨N, hN⟩ := ((tendsto_order.1 hseq').1 b hb).exists
    filter_upwards [eventually_ge_atTop ((N : ℝ) + 1)] with x hx
    refine hN.trans_le (ENNReal.ofReal_le_ofReal ?_)
    exact monotoneOn_mul_G hsupp hint (show (0:ℝ) < N + 1 by positivity)
      (show (0:ℝ) < x by linarith [show (0:ℝ) ≤ N from N.cast_nonneg]) hx
  · filter_upwards [eventually_gt_atTop 0] with x hx
    refine lt_of_le_of_lt ?_ hb
    rw [ofReal_mul_G_eq hsupp hint hx, ← lintegral_one]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_nonneg hsupp] with s hs
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one (by linarith)).2 (by linarith))

/-- **Corollary (infinite mass).** If `ρ(ℝ) = ∞` then `x·G(x) → ∞`. -/
theorem tendsto_mul_G_atTop_of_infinite (hsupp : ρ (Iio 0) = 0)
    (hint : Integrable (fun s => (1 + s)⁻¹) ρ) (hinf : ρ univ = ⊤) :
    Tendsto (fun x => x * G ρ x) atTop atTop := by
  have h := tendsto_ofReal_mul_G hsupp hint
  rw [hinf] at h
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [h.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top : ENNReal.ofReal M < ⊤))]
    with x hx
  exact ((ENNReal.ofReal_lt_ofReal_iff'.1 hx).1).le

/-- **Corollary (finite mass).** If `ρ(ℝ) < ∞` then `x·G(x) → ρ(ℝ)` in `ℝ`. -/
theorem tendsto_mul_G_of_finite (hsupp : ρ (Iio 0) = 0)
    (hint : Integrable (fun s => (1 + s)⁻¹) ρ) (hfin : ρ univ ≠ ⊤) :
    Tendsto (fun x => x * G ρ x) atTop (𝓝 (ρ univ).toReal) := by
  refine ((ENNReal.tendsto_toReal hfin).comp (tendsto_ofReal_mul_G hsupp hint)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp]
  exact ENNReal.toReal_ofReal (mul_nonneg hx.le (G_nonneg hsupp hint hx))

/-! ### 3. No representation when `x f(x) → 0` or when `x f(x)` decreases somewhere -/

/-- Quantitative lower bound from monotonicity: `x·G(x) ≥ x₀·G(x₀) > 0` for `x ≥ x₀ > 0`. -/
theorem mul_G_ge_of_le (hsupp : ρ (Iio 0) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ)
    (hρ : ρ ≠ 0) {x₀ x : ℝ} (hx₀ : 0 < x₀) (hle : x₀ ≤ x) :
    0 < x₀ * G ρ x₀ ∧ x₀ * G ρ x₀ ≤ x * G ρ x :=
  ⟨mul_G_pos hsupp hint hρ hx₀,
    monotoneOn_mul_G hsupp hint hx₀ (show (0:ℝ) < x from lt_of_lt_of_le hx₀ hle) hle⟩

/-- **No representation for `G = o(1/x)`.** If `x f(x) → 0` as `x → ∞`, no nonzero positive
measure `ρ` on `[0,∞)` with `∫ (1+s)⁻¹ dρ < ∞` has `G ρ = f` on `(0,∞)`. -/
theorem no_representation_of_tendsto_zero {f : ℝ → ℝ}
    (hf : Tendsto (fun x => x * f x) atTop (𝓝 0)) :
    ¬ ∃ ρ : Measure ℝ, ρ (Iio 0) = 0 ∧ Integrable (fun s => (1 + s)⁻¹) ρ ∧ ρ ≠ 0 ∧
      ∀ x > 0, G ρ x = f x := by
  rintro ⟨ρ, hsupp, hint, hρ, hG⟩
  have hc := mul_G_pos hsupp hint hρ one_pos
  obtain ⟨x, hx1, hx2⟩ :=
    ((hf.eventually (gt_mem_nhds hc)).and (eventually_ge_atTop (1 : ℝ))).exists
  have := (mul_G_ge_of_le hsupp hint hρ one_pos hx2).2
  rw [hG x (by linarith)] at this
  linarith

/-- **No representation if `x f(x)` strictly decreases somewhere on `(0,∞)`.** -/
theorem no_representation_of_decrease {f : ℝ → ℝ}
    (hdec : ∃ x y : ℝ, 0 < x ∧ x < y ∧ y * f y < x * f x) :
    ¬ ∃ ρ : Measure ℝ, ρ (Iio 0) = 0 ∧ Integrable (fun s => (1 + s)⁻¹) ρ ∧
      ∀ x > 0, G ρ x = f x := by
  rintro ⟨ρ, hsupp, hint, hG⟩
  obtain ⟨x, y, hx, hxy, hlt⟩ := hdec
  have := monotoneOn_mul_G hsupp hint hx (show (0:ℝ) < y by linarith) hxy.le
  simp only at this
  rw [hG x hx, hG y (by linarith)] at this
  linarith

/-- For `a > 0`, `exp(-a x)/x` has no such representation, even allowing `ρ = 0` and
infinite `ρ` (the strict decrease of `x f(x) = exp(-a x)` already rules it out). -/
theorem no_representation_exp_div {a : ℝ} (ha : 0 < a) :
    ¬ ∃ ρ : Measure ℝ, ρ (Iio 0) = 0 ∧ Integrable (fun s => (1 + s)⁻¹) ρ ∧
      ∀ x > 0, G ρ x = Real.exp (-a * x) / x := by
  refine no_representation_of_decrease ⟨1, 2, one_pos, one_lt_two, ?_⟩
  rw [mul_div_cancel₀ _ (two_ne_zero), mul_div_cancel₀ _ one_ne_zero]
  exact Real.exp_lt_exp.2 (by linarith)

/-! ### 4. Quantitative relative-error bound and its sharpness -/

lemma tanh_half_eq (d : ℝ) :
    Real.tanh (d / 2) = (1 - Real.exp (-d)) / (1 + Real.exp (-d)) := by
  rw [Real.tanh_eq]
  have hp : 0 < Real.exp (-(d / 2)) := Real.exp_pos _
  have h1 : Real.exp (d / 2) = (Real.exp (-(d / 2)))⁻¹ := by rw [Real.exp_neg, inv_inv]
  have h2 : Real.exp (-d) = Real.exp (-(d / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h1, h2]
  field_simp

/-- Pure real lemma behind the bound: if `h(x) ≤ h(y)` and `h(t)·e^{a t}` is within `ε` of `1`
at `t = x` and `t = y`, then `ε ≥ tanh(a(y-x)/2)`. (No sign conditions are needed.) -/
lemma tanh_le_of_le {h : ℝ → ℝ} {a x y ε : ℝ} (hxy : h x ≤ h y)
    (hex : |h x * Real.exp (a * x) - 1| ≤ ε) (hey : |h y * Real.exp (a * y) - 1| ≤ ε) :
    Real.tanh (a * (y - x) / 2) ≤ ε := by
  set q := Real.exp (-(a * (y - x))) with hq_def
  have hq : 0 < q := Real.exp_pos _
  have hprod : Real.exp (a * y) * q = Real.exp (a * x) := by
    rw [hq_def, ← Real.exp_add]; ring_nf
  set u := h x * Real.exp (a * x)
  set w := h y * Real.exp (a * y)
  have huw : u ≤ w * q := by
    have : w * q = h y * Real.exp (a * x) := by rw [← hprod]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hxy (Real.exp_pos _).le
  have hu := (abs_le.1 hex).1
  have hw := (abs_le.1 hey).2
  have hwq : w * q ≤ (1 + ε) * q := mul_le_mul_of_nonneg_right (by linarith) hq.le
  rw [tanh_half_eq, ← hq_def, div_le_iff₀ (by linarith)]
  nlinarith

/-- The relative error of `G` against `f(t) = exp(-a t)/t`, rewritten. -/
lemma G_div_eq (ρ : Measure ℝ) (a t : ℝ) :
    G ρ t / (Real.exp (-a * t) / t) = t * G ρ t * Real.exp (a * t) := by
  rw [div_div_eq_mul_div, neg_mul, Real.exp_neg, div_inv_eq_mul]; ring

/-- **Quantitative bound.** For any positive `ρ` on `[0,∞)` with `∫ (1+s)⁻¹ dρ < ∞` and any
`0 < x ≤ y`: if the relative error `|G(t)/f(t) - 1|` with `f(t) = exp(-a t)/t` is at most `ε`
for all `t ∈ [x,y]`, then `ε ≥ tanh(a(y-x)/2)`. (Only the endpoints are used.) -/
theorem tanh_le_rel_error (hsupp : ρ (Iio 0) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ)
    {a x y ε : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (herr : ∀ t ∈ Icc x y, |G ρ t / (Real.exp (-a * t) / t) - 1| ≤ ε) :
    Real.tanh (a * (y - x) / 2) ≤ ε := by
  have h1 := herr x ⟨le_rfl, hxy⟩
  have h2 := herr y ⟨hxy, le_rfl⟩
  rw [G_div_eq] at h1 h2
  exact tanh_le_of_le (h := fun t => t * G ρ t)
    (monotoneOn_mul_G hsupp hint hx (show (0:ℝ) < y from lt_of_lt_of_le hx hxy) hxy) h1 h2

lemma G_smul_dirac (c : NNReal) (t : ℝ) : G ((c : NNReal) • Measure.dirac (0 : ℝ)) t = c * t⁻¹ := by
  rw [G, integral_smul_nnreal_measure, integral_dirac, add_zero, NNReal.smul_def, smul_eq_mul]

/-- **Sharpness.** For `a ≥ 0` and `0 < x ≤ y` the point mass `ρ = c δ₀`,
`c = 2 e^{-a x} e^{-a y} / (e^{-a x} + e^{-a y})` (so `G(t) = c/t`), has relative error
`≤ tanh(a(y-x)/2)` on all of `[x,y]`, with equality at both endpoints. Together with
`tanh_le_rel_error`, the infimum over admissible `ρ` of the uniform relative error on `[x,y]`
is exactly `tanh(a(y-x)/2)`, and it is attained. -/
theorem rel_error_sharp {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 < x) (hxy : x ≤ y) :
    ∃ c : ℝ, 0 < c ∧
      c = 2 * Real.exp (-a * x) * Real.exp (-a * y) / (Real.exp (-a * x) + Real.exp (-a * y)) ∧
      let ρ := (Real.toNNReal c) • Measure.dirac (0 : ℝ)
      ρ (Iio 0) = 0 ∧ Integrable (fun s => (1 + s)⁻¹) ρ ∧ ρ ≠ 0 ∧
      (∀ t ∈ Icc x y,
        |G ρ t / (Real.exp (-a * t) / t) - 1| ≤ Real.tanh (a * (y - x) / 2)) ∧
      |G ρ x / (Real.exp (-a * x) / x) - 1| = Real.tanh (a * (y - x) / 2) ∧
      |G ρ y / (Real.exp (-a * y) / y) - 1| = Real.tanh (a * (y - x) / 2) := by
  set q := Real.exp (-(a * (y - x))) with hq_def
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  set c := 2 * q / (1 + q) * Real.exp (-a * x) with hc_def
  have hcpos : 0 < c := by positivity
  have hexy : Real.exp (-a * y) = q * Real.exp (-a * x) := by
    rw [hq_def, ← Real.exp_add]; ring_nf
  have hceq : c = 2 * Real.exp (-a * x) * Real.exp (-a * y) /
      (Real.exp (-a * x) + Real.exp (-a * y)) := by
    rw [hexy, hc_def]
    have : 0 < Real.exp (-a * x) := Real.exp_pos _
    field_simp
  -- error at a point `t > 0`
  have herr : ∀ t, 0 < t → G ((Real.toNNReal c) • Measure.dirac (0 : ℝ)) t /
      (Real.exp (-a * t) / t) - 1 = (2 * q * Real.exp (a * (t - x)) - (1 + q)) / (1 + q) := by
    intro t ht
    rw [G_div_eq, G_smul_dirac, Real.coe_toNNReal _ hcpos.le, hc_def]
    have : Real.exp (-a * x) * Real.exp (a * t) = Real.exp (a * (t - x)) := by
      rw [← Real.exp_add]; ring_nf
    field_simp
    rw [← this]; ring_nf
  have htanh : Real.tanh (a * (y - x) / 2) = (1 - q) / (1 + q) := by
    rw [tanh_half_eq]
  have habs : ∀ t, 0 < t → |G ((Real.toNNReal c) • Measure.dirac (0 : ℝ)) t /
      (Real.exp (-a * t) / t) - 1| = |2 * q * Real.exp (a * (t - x)) - (1 + q)| / (1 + q) := by
    intro t ht
    rw [herr t ht, abs_div, abs_of_pos (by linarith : (0:ℝ) < 1 + q)]
  refine ⟨c, hcpos, hceq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, Measure.dirac_apply' _ measurableSet_Iio]
    simp
  · exact (integrable_dirac (by simp)).smul_measure_nnreal
  · intro h0
    have := congrArg (fun μ : Measure ℝ => μ univ) h0
    simp only [smul_apply, measure_univ, FunLike.coe_zero, Pi.zero_apply] at this
    simp [Real.toNNReal_eq_zero, hcpos.not_ge] at this
  · intro t ht
    rw [habs t (by linarith [ht.1]), htanh]
    refine div_le_div_of_nonneg_right ?_ (by linarith)
    have he1 : 1 ≤ Real.exp (a * (t - x)) := Real.one_le_exp (by nlinarith [ht.1])
    have he2 : q * Real.exp (a * (t - x)) ≤ 1 := by
      rw [hq_def, ← Real.exp_add]
      exact Real.exp_le_one_iff.2 (by nlinarith [ht.2])
    rw [abs_le]; constructor <;> nlinarith
  · rw [habs x hx, htanh, sub_self, mul_zero, Real.exp_zero, mul_one]
    rw [abs_of_nonpos (by linarith)]; ring_nf
  · rw [habs y (by linarith), htanh]
    have : q * Real.exp (a * (y - x)) = 1 := by
      rw [hq_def, ← Real.exp_add]; simp
    rw [show 2 * q * Real.exp (a * (y - x)) = 2 * (q * Real.exp (a * (y - x))) by ring, this,
      abs_of_nonneg (by linarith)]
    ring

/-! ### 5. Operator-valued (matrix) version: finitely many PSD atoms -/

section Matrix

open Matrix
open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n ι : Type*} [Fintype n] [Fintype ι]

/-- Matrix Stieltjes transform of `ρ = ∑_k δ_{s_k} P_k`: `G(x) = ∑_k (x+s_k)⁻¹ P_k`. -/
noncomputable def Gmat (s : ι → ℝ) (P : ι → Matrix n n 𝕜) (x : ℝ) : Matrix n n 𝕜 :=
  ∑ k, (x + s k)⁻¹ • P k

/-- **Loewner monotonicity.** For PSD atoms `P_k` at `s_k ≥ 0` and `0 < x ≤ y`,
`y G(y) - x G(x)` is positive semidefinite. -/
theorem loewner_mono_mul_Gmat {s : ι → ℝ} {P : ι → Matrix n n 𝕜} (hs : ∀ k, 0 ≤ s k)
    (hP : ∀ k, (P k).PosSemidef) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (y • Gmat s P y - x • Gmat s P x).PosSemidef := by
  have : y • Gmat s P y - x • Gmat s P x =
      ∑ k, (y * (y + s k)⁻¹ - x * (x + s k)⁻¹) • P k := by
    simp only [Gmat, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, sub_smul]
  rw [this]
  refine posSemidef_sum _ fun k _ => (hP k).smul ?_
  have hsk := hs k
  rw [sub_nonneg, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Real quadratic form `v* P_k v` (real and `≥ 0` for PSD `P_k`). -/
noncomputable def qf (P : ι → Matrix n n 𝕜) (v : n → 𝕜) (k : ι) : ℝ :=
  RCLike.re (star v ⬝ᵥ (P k *ᵥ v))

lemma qf_nonneg {P : ι → Matrix n n 𝕜} (hP : ∀ k, (P k).PosSemidef) (v : n → 𝕜) (k : ι) :
    0 ≤ qf P v k := (RCLike.nonneg_iff.1 ((hP k).dotProduct_mulVec_nonneg v)).1

lemma qf_eq {P : ι → Matrix n n 𝕜} (hP : ∀ k, (P k).PosSemidef) (v : n → 𝕜) (k : ι) :
    ((qf P v k : ℝ) : 𝕜) = star v ⬝ᵥ (P k *ᵥ v) := by
  have him := (RCLike.nonneg_iff.1 ((hP k).dotProduct_mulVec_nonneg v)).2
  conv_rhs => rw [← RCLike.re_add_im (star v ⬝ᵥ (P k *ᵥ v))]
  simp [qf, him]

/-- Polarisation of the matrix transform: `v* G(x) v = ∑_k (x+s_k)⁻¹ v* P_k v` (a real number). -/
lemma polarisation_Gmat {s : ι → ℝ} {P : ι → Matrix n n 𝕜} (hP : ∀ k, (P k).PosSemidef)
    (v : n → 𝕜) (x : ℝ) :
    star v ⬝ᵥ (Gmat s P x *ᵥ v) = ((∑ k, (x + s k)⁻¹ * qf P v k : ℝ) : 𝕜) := by
  simp only [Gmat, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    RCLike.ofReal_sum, RCLike.ofReal_mul, qf_eq hP, RCLike.real_smul_eq_coe_mul]

/-- The scalar measure `ρ_v = ∑_k (v* P_k v) δ_{s_k}` of a polarisation `v`. -/
noncomputable def rhoPol (s : ι → ℝ) (P : ι → Matrix n n 𝕜) (v : n → 𝕜) : Measure ℝ :=
  ∑ k, (qf P v k).toNNReal • Measure.dirac (s k)

lemma integrable_finset_sum_dirac (S : Finset ι) (c : ι → NNReal) (s : ι → ℝ) (f : ℝ → ℝ) :
    Integrable f (∑ k ∈ S, c k • Measure.dirac (s k)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.sum_insert hk]
    exact ((integrable_dirac (by simp)).smul_measure_nnreal).add_measure ih

lemma integral_finset_sum_dirac (S : Finset ι) (c : ι → NNReal) (s : ι → ℝ) (f : ℝ → ℝ) :
    ∫ t, f t ∂(∑ k ∈ S, c k • Measure.dirac (s k)) = ∑ k ∈ S, (c k : ℝ) * f (s k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      integral_add_measure ((integrable_dirac (by simp)).smul_measure_nnreal)
        (integrable_finset_sum_dirac S c s f), ih, integral_smul_nnreal_measure, integral_dirac,
      NNReal.smul_def, smul_eq_mul]

/-- **Polarisations are scalar Stieltjes transforms.** For PSD atoms at `s_k ≥ 0`, the measure
`ρ_v` is supported in `[0,∞)`, satisfies `∫ (1+s)⁻¹ dρ_v < ∞`, and
`G ρ_v x = Re (v* G(x) v)`, while `v* G(x) v` is real. -/
theorem polarisation_is_stieltjes {s : ι → ℝ} {P : ι → Matrix n n 𝕜} (hs : ∀ k, 0 ≤ s k)
    (hP : ∀ k, (P k).PosSemidef) (v : n → 𝕜) :
    rhoPol s P v (Iio 0) = 0 ∧ Integrable (fun t => (1 + t)⁻¹) (rhoPol s P v) ∧
      ∀ x, (G (rhoPol s P v) x : 𝕜) = star v ⬝ᵥ (Gmat s P x *ᵥ v) := by
  refine ⟨?_, integrable_finset_sum_dirac _ _ _ _, fun x => ?_⟩
  · have hk : ∀ k, s k ∉ Iio (0 : ℝ) := fun k => by simpa using hs k
    simp [rhoPol, Measure.dirac_apply' _ measurableSet_Iio, hk]
  · rw [polarisation_Gmat hP, G, rhoPol, integral_finset_sum_dirac]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.coe_toNNReal _ (qf_nonneg hP v k)]; ring

/-- **Matrix no-go.** For `a > 0`, no matrix propagator `G(x) = ∑_k (x+s_k)⁻¹ P_k` with PSD
`P_k` and `s_k ≥ 0` has a polarisation component `v* G(x) v = exp(-a x)/x` for all `x > 0`. -/
theorem matrix_no_representation_exp_div {a : ℝ} (ha : 0 < a) {s : ι → ℝ}
    {P : ι → Matrix n n 𝕜} (hs : ∀ k, 0 ≤ s k) (hP : ∀ k, (P k).PosSemidef) (v : n → 𝕜) :
    ¬ ∀ x > 0, star v ⬝ᵥ (Gmat s P x *ᵥ v) = ((Real.exp (-a * x) / x : ℝ) : 𝕜) := by
  intro h
  obtain ⟨h1, h2, h3⟩ := polarisation_is_stieltjes hs hP v
  refine no_representation_exp_div ha ⟨rhoPol s P v, h1, h2, fun x hx => ?_⟩
  exact_mod_cast (h3 x).trans (h x hx)

/-- **Matrix tanh bound, per polarisation.** If `v* G(t) v` (which is real) has relative error
at most `ε` against `exp(-a t)/t` on `[x,y]`, `0 < x ≤ y`, then `ε ≥ tanh(a(y-x)/2)`. -/
theorem matrix_tanh_le_rel_error {s : ι → ℝ} {P : ι → Matrix n n 𝕜} (hs : ∀ k, 0 ≤ s k)
    (hP : ∀ k, (P k).PosSemidef) (v : n → 𝕜) {a x y ε : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (herr : ∀ t ∈ Icc x y,
      |RCLike.re (star v ⬝ᵥ (Gmat s P t *ᵥ v)) / (Real.exp (-a * t) / t) - 1| ≤ ε) :
    Real.tanh (a * (y - x) / 2) ≤ ε := by
  obtain ⟨h1, h2, h3⟩ := polarisation_is_stieltjes hs hP v
  refine tanh_le_rel_error h1 h2 hx hxy fun t ht => ?_
  have := herr t ht
  rwa [← h3 t, RCLike.ofReal_re] at this

end Matrix

end APEX.Spectral.Strong

