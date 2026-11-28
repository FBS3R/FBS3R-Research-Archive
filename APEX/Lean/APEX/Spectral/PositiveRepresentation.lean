import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Positive (Stieltjes) representations `G(x) = ∫ (x+s)⁻¹ dρ(s)`

Setting: `ρ : Measure ℝ` a **finite** positive measure with `ρ (Iio 0) = 0` (support in `[0,∞)`),
and `G ρ x = ∫ s, (x+s)⁻¹ ∂ρ` (used for `x > 0`). Finiteness of `ρ` is assumed throughout
(the locally finite case with `∫ 1/(1+s) dρ < ∞` is not treated).

* `exists_Icc_pos`: if `ρ ≠ 0` there is `M ≥ 0` with `ρ([0,M]) > 0`.
* `mul_G_ge`: for `x > 0`, `x/(x+M) · ρ([0,M]) ≤ x·G(x)`.
* `liminf_mul_G_pos`: for some `M ≥ 0`, `m = ρ([0,M]) > 0` and every `c < m` satisfies
  `c ≤ x·G(x)` eventually as `x → ∞` (i.e. `liminf x G(x) ≥ m`).
* `not_tendsto_mul_G_zero`: `x·G(x)` does not tend to `0`.
* `no_representation_exp_div`: for `a > 0` no nonzero such `ρ` has `G(x) = exp(-a x)/x` for all `x > 0`.
* `tendsto_mul_G`: `x·G(x) → ρ(ℝ) (= ρ([0,∞)))` as `x → ∞`.
-/

open MeasureTheory Filter Topology Set

namespace APEX.Spectral

/-- Stieltjes-type transform `G(x) = ∫ (x+s)⁻¹ dρ(s)`. -/
noncomputable def G (ρ : Measure ℝ) (x : ℝ) : ℝ := ∫ s, (x + s)⁻¹ ∂ρ

variable {ρ : Measure ℝ}

lemma ae_nonneg (hsupp : ρ (Iio 0) = 0) : ∀ᵐ s ∂ρ, 0 ≤ s := by
  rw [ae_iff]; convert hsupp using 2; ext s; simp

lemma exists_Icc_pos (hsupp : ρ (Iio 0) = 0) (hρ : ρ ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ 0 < ρ (Icc 0 M) := by
  by_contra h
  push Not at h
  have h0 : ∀ n : ℕ, ρ (Icc 0 (n : ℝ)) = 0 := fun n =>
    le_antisymm (h n (Nat.cast_nonneg n)) bot_le
  have hU : (⋃ n : ℕ, Icc (0 : ℝ) n) = Ici 0 := by
    ext s; simp only [mem_iUnion, mem_Icc, mem_Ici]
    constructor
    · rintro ⟨n, h1, _⟩; exact h1
    · intro hs; obtain ⟨n, hn⟩ := exists_nat_ge s; exact ⟨n, hs, hn⟩
  have hI : ρ (Ici 0) = 0 := by rw [← hU]; exact measure_iUnion_null h0
  apply hρ
  rw [← Measure.measure_univ_eq_zero]
  have : (univ : Set ℝ) = Iio 0 ∪ Ici 0 := by ext s; simp
  rw [this]; exact le_antisymm ((measure_union_le _ _).trans (by simp [hsupp, hI])) bot_le

lemma integrable_inv_add [IsFiniteMeasure ρ] (hsupp : ρ (Iio 0) = 0) {x : ℝ} (hx : 0 < x) :
    Integrable (fun s => (x + s)⁻¹) ρ := by
  refine Integrable.mono' (integrable_const x⁻¹) ?_ ?_
  · exact (measurable_const.add measurable_id).inv.aestronglyMeasurable
  · filter_upwards [ae_nonneg hsupp] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by linarith))]
    exact inv_anti₀ hx (by linarith)

lemma mul_G_eq [IsFiniteMeasure ρ] (x : ℝ) : x * G ρ x = ∫ s, x / (x + s) ∂ρ := by
  rw [G, ← integral_const_mul]; rfl

/-- **(i) Elementary lower bound.** For a finite positive measure `ρ` on `[0,∞)`, any `M ≥ 0`
and `x > 0`: `x·G(x) ≥ x/(x+M) · ρ([0,M])`. -/
theorem mul_G_ge [IsFiniteMeasure ρ] (hsupp : ρ (Iio 0) = 0) {M x : ℝ}
    (hx : 0 < x) : x / (x + M) * (ρ (Icc 0 M)).toReal ≤ x * G ρ x := by
  rw [mul_G_eq]
  have hint : Integrable (fun s => x / (x + s)) ρ := by
    simpa [div_eq_mul_inv] using (integrable_inv_add hsupp hx).const_mul x
  calc x / (x + M) * (ρ (Icc 0 M)).toReal
      = ∫ s, (Icc 0 M).indicator (fun _ => x / (x + M)) s ∂ρ := by
        rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_comm, measureReal_def]
    _ ≤ ∫ s, x / (x + s) ∂ρ := by
        refine integral_mono_ae ((integrable_const _).indicator measurableSet_Icc) hint ?_
        filter_upwards [ae_nonneg hsupp] with s hs
        by_cases hsM : s ∈ Icc 0 M
        · rw [indicator_of_mem hsM]
          exact div_le_div_of_nonneg_left hx.le (by linarith) (by linarith [hsM.2])
        · rw [indicator_of_notMem hsM]; positivity

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

/-- **(i) Liminf form.** If `ρ` is a nonzero finite positive measure on `[0,∞)`, there is `M ≥ 0`
with `m := ρ([0,M]) > 0` such that for every `c < m`, eventually (as `x → ∞`) `c ≤ x·G(x)`;
i.e. `liminf_{x→∞} x G(x) ≥ m > 0`. -/
theorem liminf_mul_G_pos [IsFiniteMeasure ρ] (hsupp : ρ (Iio 0) = 0) (hρ : ρ ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ 0 < (ρ (Icc 0 M)).toReal ∧
      ∀ c < (ρ (Icc 0 M)).toReal, ∀ᶠ x in atTop, c ≤ x * G ρ x := by
  obtain ⟨M, hM, hpos⟩ := exists_Icc_pos hsupp hρ
  have hm : 0 < (ρ (Icc 0 M)).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  refine ⟨M, hM, hm, fun c hc => ?_⟩
  set m := (ρ (Icc 0 M)).toReal
  have hlim : Tendsto (fun x : ℝ => x / (x + M) * m) atTop (𝓝 (1 * m)) :=
    (tendsto_div_add M).mul_const _
  rw [one_mul] at hlim
  filter_upwards [hlim.eventually (eventually_gt_nhds hc), eventually_gt_atTop 0] with x h1 h2
  exact h1.le.trans (mul_G_ge hsupp h2)

/-- **(i) Consequence.** `x·G(x)` does not tend to `0` as `x → ∞`. -/
theorem not_tendsto_mul_G_zero [IsFiniteMeasure ρ] (hsupp : ρ (Iio 0) = 0) (hρ : ρ ≠ 0) :
    ¬ Tendsto (fun x => x * G ρ x) atTop (𝓝 0) := by
  intro h
  obtain ⟨M, -, hm, hev⟩ := liminf_mul_G_pos hsupp hρ
  have h1 := hev ((ρ (Icc 0 M)).toReal / 2) (by linarith)
  have h2 := h.eventually (gt_mem_nhds (half_pos hm))
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  linarith

/-- **(ii) Corollary.** For `a > 0` there is no nonzero finite positive measure `ρ` on `[0,∞)`
with `G(x) = exp(-a x)/x` for all `x > 0` (since then `x·G(x) = exp(-a x) → 0`). -/
theorem no_representation_exp_div {a : ℝ} (ha : 0 < a) :
    ¬ ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ ρ (Iio 0) = 0 ∧ ρ ≠ 0 ∧
      ∀ x > 0, G ρ x = Real.exp (-a * x) / x := by
  rintro ⟨ρ, hfin, hsupp, hρ, hG⟩
  apply not_tendsto_mul_G_zero hsupp hρ
  have hlin : Tendsto (fun x : ℝ => -a * x) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  refine (Real.tendsto_exp_atBot.comp hlin).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp, hG x hx]
  field_simp

/-- **(iii) Exact limit.** For a finite positive measure `ρ` on `[0,∞)`,
`x·G(x) → ρ([0,∞)) = ρ(ℝ)` as `x → ∞` (dominated convergence with bound `1`). -/
theorem tendsto_mul_G [IsFiniteMeasure ρ] (hsupp : ρ (Iio 0) = 0) :
    Tendsto (fun x => x * G ρ x) atTop (𝓝 (ρ univ).toReal) := by
  have key : Tendsto (fun x : ℝ => ∫ s, x / (x + s) ∂ρ) atTop (𝓝 (∫ _, (1 : ℝ) ∂ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun x =>
        (measurable_const.div (measurable_const.add measurable_id)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with x hx
      filter_upwards [ae_nonneg hsupp] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_le_one (by linarith)).2 (by linarith)
    · filter_upwards [ae_nonneg hsupp] with s hs
      exact tendsto_div_add s
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def] at key
  refine key.congr' ?_
  filter_upwards with x
  rw [mul_G_eq]

end APEX.Spectral

