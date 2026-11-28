import APEX.Spectral.Strengthened

/-!
# Threshold-strengthened spectral bound (strengthening of SPC-4)

We reuse `APEX.Spectral.Strong.G ρ x = ∫ (x+s)⁻¹ dρ(s)` from `Strengthened.lean`, now for a
positive measure `ρ` on `ℝ` supported on `[s₀,∞)` (`ρ (Iio s₀) = 0`) with a **threshold**
`s₀ ≥ 0`, under the same integrability hypothesis `Integrable (fun s => (1+s)⁻¹) ρ`
(`ρ` may be infinite). We also treat the measure-free finite-atom transform
`Gfin w s x = ∑_k w_k/(x+s_k)` with `w_k ≥ 0`, `s_k ≥ s₀`.

Notation: `f a z = exp(-a z)/z`, `D a s₀ x y = a(y-x) + log(y(x+s₀)/(x(y+s₀)))`,
`φ a s₀ z = z/(z+s₀) · exp(a z)`.

**Results** (always `0 ≤ s₀`, `0 < x ≤ y`):
1. `threshold_mono` / `threshold_ratio` (measure) and `threshold_mono_fin` (finite atoms):
   `G(y) ≥ (x+s₀)/(y+s₀) · G(x)`, hence `G(y)/G(x) ≥ (x+s₀)/(y+s₀)` when `G(x) > 0`.
   `G_atoms`: the atomic measure `∑ w_k δ_{s_k}` has `G = Gfin w s`.
2. `tanh_le_threshold` (and `_fin`): for **any real** `a` and any `ε`, if
   `(1-ε) f(x) ≤ G(x)` and `G(y) ≤ (1+ε) f(y)` (only these two one-sided bounds are used; no
   `ε < 1` needed), then `ε ≥ tanh(D/2)`. `tanh_le_threshold_two_sided` is the form with both
   bounds at both points; `tanh_le_rel_error_threshold` (and `_fin`): if
   `|G(t)/f(t) - 1| ≤ ε` for all `t ∈ [x,y]` then `ε ≥ tanh(D/2)`.
3. `one_atom_attains` (measure) and `one_atom_attains_fin` (one atom): for `a ≥ 0` the measure
   `w δ_{s₀}` with `w = 2/(φ(x)+φ(y))` (balancing the endpoint errors: `G/f = 1 - tanh(D/2)` at
   `x`, `= 1 + tanh(D/2)` at `y`) has `|G(t)/f(t) - 1| ≤ tanh(D/2)` on all of `[x,y]`, with
   equality at both endpoints (`G/f = w φ` is non-decreasing on `(0,∞)` for `a ≥ 0`).
   **Sharpness**: `sharp_threshold` — `tanh(D/2)` is the least `ε` such that some admissible
   measure (`ρ (Iio s₀) = 0`, `∫ (1+s)⁻¹ dρ < ∞`) has uniform relative error `≤ ε` on `[x,y]`
   (`IsLeast`), i.e. the infimum over admissible measures of the sup relative error equals
   `tanh(D/2)` and is attained; `sharp_threshold_fin` — the same over finite-atom measures
   (`n` atoms, weights `≥ 0`, positions `≥ s₀`), proved without measure theory.
4. Consistency with SPC-4: `D_zero` (`D a 0 x y = a(y-x)`), `recovers_SPC4` (re-derives
   `Strong.tanh_le_rel_error` from the threshold theorem at `s₀ = 0`), `sharp_threshold_zero`
   (the `IsLeast` value at `s₀ = 0` is `tanh(a(y-x)/2)`, matching `Strong.rel_error_sharp`),
   and `strengthens_SPC4` / `strengthens_SPC4_strict`: `tanh(a(y-x)/2) ≤ tanh(D/2)`, strictly
   if `s₀ > 0` and `x < y`.

**Physical caveat.** These are necessary conditions on *candidate* propagators of
Källén–Lehmann type with a spectral threshold `s₀` (mass gap): they quantify how well a
positive superposition of free propagators `1/(x+s)`, `s ≥ s₀`, can approximate
`exp(-a x)/x` on a Euclidean window `[x,y]`. They filter candidate propagators only and say
nothing about the (non-perturbative) existence or consistency of any quantum field theory or
theory of quantum gravity.
-/

open MeasureTheory Set

namespace APEX.Spectral.Threshold

open APEX.Spectral.Strong (G)

/-- Target propagator `f(z) = exp(-a z)/z`. -/
noncomputable def f (a z : ℝ) : ℝ := Real.exp (-a * z) / z

/-- Exponent of the threshold bound: `D = a(y-x) + log(y(x+s₀)/(x(y+s₀)))`. -/
noncomputable def D (a s₀ x y : ℝ) : ℝ :=
  a * (y - x) + Real.log (y * (x + s₀) / (x * (y + s₀)))

/-- `φ(z) = z/(z+s₀) · exp(a z)`, so that `(w/(z+s₀))/f(z) = w φ(z)`. -/
noncomputable def φ (a s₀ z : ℝ) : ℝ := z / (z + s₀) * Real.exp (a * z)

/-- Finite-atom transform `∑_k w_k/(x+s_k)`. -/
noncomputable def Gfin {ι : Type*} [Fintype ι] (w s : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ k, w k / (x + s k)

lemma f_pos (a : ℝ) {z : ℝ} (hz : 0 < z) : 0 < f a z := by unfold f; positivity

/-! ### 1. Threshold monotonicity -/

/-- Pointwise inequality: `(x+s₀)/(y+s₀) · (x+s)⁻¹ ≤ (y+s)⁻¹` for `s ≥ s₀ ≥ 0`, `0 < x ≤ y`. -/
lemma ratio_le_inv {s₀ s x y : ℝ} (hs₀ : 0 ≤ s₀) (hs : s₀ ≤ s) (hx : 0 < x) (hxy : x ≤ y) :
    (x + s₀) / (y + s₀) * (x + s)⁻¹ ≤ (y + s)⁻¹ := by
  rw [← div_eq_mul_inv, div_div, inv_eq_one_div,
    div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith), one_mul]
  nlinarith

/-- **Threshold monotonicity (measure).** -/
theorem threshold_mono {ρ : Measure ℝ} {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (hsupp : ρ (Iio s₀) = 0)
    (hint : Integrable (fun s => (1 + s)⁻¹) ρ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (x + s₀) / (y + s₀) * G ρ x ≤ G ρ y := by
  have hsupp0 : ρ (Iio 0) = 0 := measure_mono_null (Iio_subset_Iio hs₀) hsupp
  have hae : ∀ᵐ s ∂ρ, s₀ ≤ s := by
    rw [ae_iff]; convert hsupp using 2; ext s; simp
  rw [G, G, ← integral_const_mul]
  refine integral_mono_ae ((Strong.integrable_inv_add hsupp0 hint hx).const_mul _)
    (Strong.integrable_inv_add hsupp0 hint (by linarith)) ?_
  filter_upwards [hae] with s hs
  exact ratio_le_inv hs₀ hs hx hxy

/-- **Threshold monotonicity, ratio form.** -/
theorem threshold_ratio {ρ : Measure ℝ} {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (hsupp : ρ (Iio s₀) = 0)
    (hint : Integrable (fun s => (1 + s)⁻¹) ρ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hG : 0 < G ρ x) : (x + s₀) / (y + s₀) ≤ G ρ y / G ρ x := by
  rw [le_div_iff₀ hG]; exact threshold_mono hs₀ hsupp hint hx hxy

/-- **Threshold monotonicity (finite atoms, no measure theory).** -/
theorem threshold_mono_fin {ι : Type*} [Fintype ι] {w s : ι → ℝ} {s₀ x y : ℝ} (hs₀ : 0 ≤ s₀)
    (hw : ∀ k, 0 ≤ w k) (hs : ∀ k, s₀ ≤ s k) (hx : 0 < x) (hxy : x ≤ y) :
    (x + s₀) / (y + s₀) * Gfin w s x ≤ Gfin w s y := by
  unfold Gfin; rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  calc (x + s₀) / (y + s₀) * (w k / (x + s k))
      = w k * ((x + s₀) / (y + s₀) * (x + s k)⁻¹) := by ring
    _ ≤ w k * (y + s k)⁻¹ := mul_le_mul_of_nonneg_left (ratio_le_inv hs₀ (hs k) hx hxy) (hw k)
    _ = w k / (y + s k) := by ring

/-- The atomic measure `∑ w_k δ_{s_k}` has transform `Gfin w s`. -/
theorem G_atoms {ι : Type*} [Fintype ι] {w s : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (z : ℝ) :
    G (∑ k, (w k).toNNReal • Measure.dirac (s k)) z = Gfin w s z := by
  rw [G, Strong.integral_finset_sum_dirac, Gfin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.coe_toNNReal _ (hw k)]; ring

/-! ### 2. The optimal relative-error lower bound -/

lemma exp_D {a s₀ x y : ℝ} (hs₀ : 0 ≤ s₀) (hx : 0 < x) (hxy : x ≤ y) :
    Real.exp (D a s₀ x y) = (x + s₀) / (y + s₀) * (f a x / f a y) := by
  have hy : 0 < y := by linarith
  rw [D, Real.exp_add, Real.exp_log (by positivity), f, f]
  have h : Real.exp (a * (y - x)) = Real.exp (-a * x) / Real.exp (-a * y) := by
    rw [← Real.exp_sub]; ring_nf
  rw [h]
  have h1 : 0 < Real.exp (-a * y) := Real.exp_pos _
  have h2 : 0 < Real.exp (-a * x) := Real.exp_pos _
  field_simp

/-- Pure real core of the bound. -/
theorem tanh_le_of_two_point {a s₀ x y ε Gx Gy : ℝ} (hs₀ : 0 ≤ s₀) (hx : 0 < x) (hxy : x ≤ y)
    (hmono : (x + s₀) / (y + s₀) * Gx ≤ Gy)
    (hlo : (1 - ε) * f a x ≤ Gx) (hhi : Gy ≤ (1 + ε) * f a y) :
    Real.tanh (D a s₀ x y / 2) ≤ ε := by
  have hy : 0 < y := by linarith
  have hr : 0 ≤ (x + s₀) / (y + s₀) := by positivity
  have hfy : 0 < f a y := f_pos a hy
  have h1 : (x + s₀) / (y + s₀) * ((1 - ε) * f a x) ≤ (1 + ε) * f a y :=
    (mul_le_mul_of_nonneg_left hlo hr).trans (hmono.trans hhi)
  have h2 : (1 - ε) * Real.exp (D a s₀ x y) ≤ 1 + ε := by
    rw [exp_D hs₀ hx hxy]
    have : (1 - ε) * ((x + s₀) / (y + s₀) * (f a x / f a y)) =
        ((x + s₀) / (y + s₀) * ((1 - ε) * f a x)) / f a y := by ring
    rw [this, div_le_iff₀ hfy]; exact h1
  set q := Real.exp (-D a s₀ x y) with hq_def
  have hq : 0 < q := Real.exp_pos _
  have hEq : Real.exp (D a s₀ x y) * q = 1 := by rw [hq_def, ← Real.exp_add]; simp
  have h3 : 1 - ε ≤ (1 + ε) * q := by
    calc 1 - ε = (1 - ε) * Real.exp (D a s₀ x y) * q := by rw [mul_assoc, hEq, mul_one]
      _ ≤ (1 + ε) * q := mul_le_mul_of_nonneg_right h2 hq.le
  rw [Strong.tanh_half_eq, ← hq_def, div_le_iff₀ (by linarith)]
  linarith

/-- **Optimal relative-error bound (measure).** Any real `a`; only the lower bound at `x` and
the upper bound at `y` are used. -/
theorem tanh_le_threshold {ρ : Measure ℝ} {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (hsupp : ρ (Iio s₀) = 0)
    (hint : Integrable (fun s => (1 + s)⁻¹) ρ) {a x y ε : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hlo : (1 - ε) * f a x ≤ G ρ x) (hhi : G ρ y ≤ (1 + ε) * f a y) :
    Real.tanh (D a s₀ x y / 2) ≤ ε :=
  tanh_le_of_two_point hs₀ hx hxy (threshold_mono hs₀ hsupp hint hx hxy) hlo hhi

/-- The two-sided form: `(1-ε) f ≤ G ≤ (1+ε) f` at `z = x` and `z = y`, `0 ≤ ε < 1`. -/
theorem tanh_le_threshold_two_sided {ρ : Measure ℝ} {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hsupp : ρ (Iio s₀) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ) {a x y ε : ℝ}
    (hx : 0 < x) (hxy : x < y) (_hε0 : 0 ≤ ε) (_hε1 : ε < 1)
    (hbx : (1 - ε) * f a x ≤ G ρ x ∧ G ρ x ≤ (1 + ε) * f a x)
    (hby : (1 - ε) * f a y ≤ G ρ y ∧ G ρ y ≤ (1 + ε) * f a y) :
    Real.tanh (D a s₀ x y / 2) ≤ ε :=
  tanh_le_threshold hs₀ hsupp hint hx hxy.le hbx.1 hby.2

lemma bounds_of_abs {u v ε : ℝ} (hv : 0 < v) (h : |u / v - 1| ≤ ε) :
    (1 - ε) * v ≤ u ∧ u ≤ (1 + ε) * v := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  constructor
  · have : 1 - ε ≤ u / v := by linarith
    rwa [le_div_iff₀ hv] at this
  · have : u / v ≤ 1 + ε := by linarith
    rwa [div_le_iff₀ hv] at this

/-- **Sup relative error on `[x,y]` (measure).** -/
theorem tanh_le_rel_error_threshold {ρ : Measure ℝ} {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hsupp : ρ (Iio s₀) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ) {a x y ε : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (herr : ∀ t ∈ Icc x y, |G ρ t / f a t - 1| ≤ ε) :
    Real.tanh (D a s₀ x y / 2) ≤ ε :=
  tanh_le_threshold hs₀ hsupp hint hx hxy
    (bounds_of_abs (f_pos a hx) (herr x ⟨le_rfl, hxy⟩)).1
    (bounds_of_abs (f_pos a (by linarith)) (herr y ⟨hxy, le_rfl⟩)).2

/-- **Optimal bound (finite atoms).** -/
theorem tanh_le_threshold_fin {ι : Type*} [Fintype ι] {w s : ι → ℝ} {s₀ a x y ε : ℝ}
    (hs₀ : 0 ≤ s₀) (hw : ∀ k, 0 ≤ w k) (hs : ∀ k, s₀ ≤ s k) (hx : 0 < x) (hxy : x ≤ y)
    (hlo : (1 - ε) * f a x ≤ Gfin w s x) (hhi : Gfin w s y ≤ (1 + ε) * f a y) :
    Real.tanh (D a s₀ x y / 2) ≤ ε :=
  tanh_le_of_two_point hs₀ hx hxy (threshold_mono_fin hs₀ hw hs hx hxy) hlo hhi

/-- **Sup relative error on `[x,y]` (finite atoms).** -/
theorem tanh_le_rel_error_threshold_fin {ι : Type*} [Fintype ι] {w s : ι → ℝ} {s₀ a x y ε : ℝ}
    (hs₀ : 0 ≤ s₀) (hw : ∀ k, 0 ≤ w k) (hs : ∀ k, s₀ ≤ s k) (hx : 0 < x) (hxy : x ≤ y)
    (herr : ∀ t ∈ Icc x y, |Gfin w s t / f a t - 1| ≤ ε) :
    Real.tanh (D a s₀ x y / 2) ≤ ε :=
  tanh_le_threshold_fin hs₀ hw hs hx hxy
    (bounds_of_abs (f_pos a hx) (herr x ⟨le_rfl, hxy⟩)).1
    (bounds_of_abs (f_pos a (by linarith)) (herr y ⟨hxy, le_rfl⟩)).2

/-! ### 3. Attainability by one atom at the threshold -/

lemma φ_pos (a : ℝ) {s₀ z : ℝ} (hs₀ : 0 ≤ s₀) (hz : 0 < z) : 0 < φ a s₀ z := by
  unfold φ; have : 0 < z + s₀ := by linarith
  positivity

/-- `φ` is non-decreasing on `(0,∞)` for `a ≥ 0` (no derivatives). -/
lemma φ_mono {a s₀ t t' : ℝ} (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀) (ht : 0 < t) (htt : t ≤ t') :
    φ a s₀ t ≤ φ a s₀ t' := by
  unfold φ
  have h1 : t / (t + s₀) ≤ t' / (t' + s₀) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have h2 : Real.exp (a * t) ≤ Real.exp (a * t') :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htt ha)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (div_nonneg (by linarith) (by linarith))

lemma one_atom_div_f (a w : ℝ) {s₀ z : ℝ} (hs₀ : 0 ≤ s₀) (hz : 0 < z) :
    w / (z + s₀) / f a z = w * φ a s₀ z := by
  unfold f φ
  have he : Real.exp (-a * z) = (Real.exp (a * z))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  have : 0 < z + s₀ := by linarith
  rw [he]; field_simp

lemma φ_ratio {a s₀ x y : ℝ} (hs₀ : 0 ≤ s₀) (hx : 0 < x) (hxy : x ≤ y) :
    φ a s₀ y = Real.exp (D a s₀ x y) * φ a s₀ x := by
  have hy : 0 < y := by linarith
  rw [D, Real.exp_add, Real.exp_log (by positivity), φ, φ]
  have h : Real.exp (a * y) = Real.exp (a * (y - x)) * Real.exp (a * x) := by
    rw [← Real.exp_add]; ring_nf
  rw [h]
  have : 0 < x + s₀ := by linarith
  have : 0 < y + s₀ := by linarith
  field_simp

/-- Real core of attainability: with `w = 2/(φ(x)+φ(y))`, `w φ` ranges in
`[1 - tanh(D/2), 1 + tanh(D/2)]` on `[x,y]` with the extreme values at the endpoints. -/
theorem attain_core {a s₀ x y : ℝ} (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀) (hx : 0 < x) (hxy : x ≤ y) :
    let w := 2 / (φ a s₀ x + φ a s₀ y)
    0 < w ∧ w * φ a s₀ x = 1 - Real.tanh (D a s₀ x y / 2) ∧
      w * φ a s₀ y = 1 + Real.tanh (D a s₀ x y / 2) ∧
      0 ≤ Real.tanh (D a s₀ x y / 2) ∧
      ∀ t ∈ Icc x y, |w * φ a s₀ t - 1| ≤ Real.tanh (D a s₀ x y / 2) := by
  intro w
  have hy : 0 < y := by linarith
  have hp := φ_pos a hs₀ hx
  have hP := φ_pos a hs₀ hy
  have hw : 0 < w := by positivity
  set E := Real.exp (D a s₀ x y) with hE_def
  have hE : 0 < E := Real.exp_pos _
  have hPE : φ a s₀ y = E * φ a s₀ x := φ_ratio hs₀ hx hxy
  have hT : Real.tanh (D a s₀ x y / 2) = (E - 1) / (E + 1) := by
    rw [Strong.tanh_half_eq, Real.exp_neg, ← hE_def]; field_simp
  have hx1 : w * φ a s₀ x = 1 - Real.tanh (D a s₀ x y / 2) := by
    simp only [w]; rw [hT, hPE]; field_simp; ring
  have hy1 : w * φ a s₀ y = 1 + Real.tanh (D a s₀ x y / 2) := by
    simp only [w]; rw [hT, hPE]; field_simp; ring
  have hmono : w * φ a s₀ x ≤ w * φ a s₀ y :=
    mul_le_mul_of_nonneg_left (φ_mono ha hs₀ hx hxy) hw.le
  refine ⟨hw, hx1, hy1, by linarith, fun t ht => ?_⟩
  have h1 := mul_le_mul_of_nonneg_left (φ_mono ha hs₀ hx ht.1) hw.le
  have h2 := mul_le_mul_of_nonneg_left (φ_mono ha hs₀ (by linarith [ht.1]) ht.2) hw.le
  rw [abs_le]; constructor <;> linarith

lemma G_smul_dirac (c : ℝ) (hc : 0 ≤ c) (s₀ t : ℝ) :
    G (c.toNNReal • Measure.dirac s₀) t = c / (t + s₀) := by
  rw [G, integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ hc, div_eq_mul_inv]

/-- **Attainability (measure).** For `a ≥ 0` the one-atom measure `w δ_{s₀}`,
`w = 2/(φ(x)+φ(y))`, is admissible and has `|G/f - 1| ≤ tanh(D/2)` on `[x,y]`, with
`G/f = 1 ∓ tanh(D/2)` at `x`, `y` (so equality of the relative error at both endpoints). -/
theorem one_atom_attains {a s₀ x y : ℝ} (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀) (hx : 0 < x) (hxy : x ≤ y) :
    ∃ w : ℝ, 0 < w ∧ w = 2 / (φ a s₀ x + φ a s₀ y) ∧
      (w.toNNReal • Measure.dirac s₀) (Iio s₀) = 0 ∧
      Integrable (fun s => (1 + s)⁻¹) (w.toNNReal • Measure.dirac s₀) ∧
      (∀ t ∈ Icc x y, |G (w.toNNReal • Measure.dirac s₀) t / f a t - 1|
        ≤ Real.tanh (D a s₀ x y / 2)) ∧
      G (w.toNNReal • Measure.dirac s₀) x / f a x = 1 - Real.tanh (D a s₀ x y / 2) ∧
      G (w.toNNReal • Measure.dirac s₀) y / f a y = 1 + Real.tanh (D a s₀ x y / 2) ∧
      |G (w.toNNReal • Measure.dirac s₀) x / f a x - 1| = Real.tanh (D a s₀ x y / 2) ∧
      |G (w.toNNReal • Measure.dirac s₀) y / f a y - 1| = Real.tanh (D a s₀ x y / 2) := by
  obtain ⟨hw, hx1, hy1, hT0, hall⟩ := attain_core ha hs₀ hx hxy
  set w := 2 / (φ a s₀ x + φ a s₀ y)
  have hdiv : ∀ t, 0 < t → G (w.toNNReal • Measure.dirac s₀) t / f a t = w * φ a s₀ t :=
    fun t ht => by rw [G_smul_dirac w hw.le, one_atom_div_f a w hs₀ ht]
  have hy : 0 < y := by linarith
  refine ⟨w, hw, rfl, ?_, (integrable_dirac (by simp)).smul_measure_nnreal, fun t ht => ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, Measure.dirac_apply' _ measurableSet_Iio]; simp
  · rw [hdiv t (by linarith [ht.1])]; exact hall t ht
  · rw [hdiv x hx, hx1]
  · rw [hdiv y hy, hy1]
  · rw [hdiv x hx, hx1, show 1 - Real.tanh (D a s₀ x y / 2) - 1 = -Real.tanh (D a s₀ x y / 2)
      by ring, abs_neg, abs_of_nonneg hT0]
  · rw [hdiv y hy, hy1, add_sub_cancel_left, abs_of_nonneg hT0]

/-- **Attainability (one atom, measure-free).** -/
theorem one_atom_attains_fin {a s₀ x y : ℝ} (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀) (hx : 0 < x)
    (hxy : x ≤ y) :
    let w : Fin 1 → ℝ := fun _ => 2 / (φ a s₀ x + φ a s₀ y)
    let s : Fin 1 → ℝ := fun _ => s₀
    (∀ k, 0 < w k) ∧ (∀ k, s₀ ≤ s k) ∧
      (∀ t ∈ Icc x y, |Gfin w s t / f a t - 1| ≤ Real.tanh (D a s₀ x y / 2)) ∧
      |Gfin w s x / f a x - 1| = Real.tanh (D a s₀ x y / 2) ∧
      |Gfin w s y / f a y - 1| = Real.tanh (D a s₀ x y / 2) := by
  intro w s
  obtain ⟨hw, hx1, hy1, hT0, hall⟩ := attain_core ha hs₀ hx hxy
  have hdiv : ∀ t, 0 < t → Gfin w s t / f a t = 2 / (φ a s₀ x + φ a s₀ y) * φ a s₀ t := by
    intro t ht
    simp only [Gfin, w, s, Finset.univ_unique, Finset.sum_singleton]
    exact one_atom_div_f a _ hs₀ ht
  have hy : 0 < y := by linarith
  refine ⟨fun _ => hw, fun _ => le_rfl, fun t ht => ?_, ?_, ?_⟩
  · rw [hdiv t (by linarith [ht.1])]; exact hall t ht
  · rw [hdiv x hx, hx1, show 1 - Real.tanh (D a s₀ x y / 2) - 1 = -Real.tanh (D a s₀ x y / 2)
      by ring, abs_neg, abs_of_nonneg hT0]
  · rw [hdiv y hy, hy1, add_sub_cancel_left, abs_of_nonneg hT0]

/-- **Sharpness (measures).** For `a ≥ 0`, `0 ≤ s₀`, `0 < x ≤ y`, `tanh(D/2)` is the least
uniform relative-error bound on `[x,y]` achievable by admissible measures supported on
`[s₀,∞)`: the infimum of the sup relative error equals `tanh(D/2)` and is attained. -/
theorem sharp_threshold {a s₀ x y : ℝ} (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀) (hx : 0 < x) (hxy : x ≤ y) :
    IsLeast {ε | ∃ ρ : Measure ℝ, ρ (Iio s₀) = 0 ∧ Integrable (fun s => (1 + s)⁻¹) ρ ∧
        ∀ t ∈ Icc x y, |G ρ t / f a t - 1| ≤ ε} (Real.tanh (D a s₀ x y / 2)) := by
  refine ⟨?_, fun ε ⟨ρ, hsupp, hint, herr⟩ =>
    tanh_le_rel_error_threshold hs₀ hsupp hint hx hxy herr⟩
  obtain ⟨w, -, -, h1, h2, h3, -⟩ := one_atom_attains ha hs₀ hx hxy
  exact ⟨_, h1, h2, h3⟩

/-- **Sharpness (finite-atom measures, measure-free).** -/
theorem sharp_threshold_fin {a s₀ x y : ℝ} (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀) (hx : 0 < x)
    (hxy : x ≤ y) :
    IsLeast {ε | ∃ (n : ℕ) (w s : Fin n → ℝ), (∀ k, 0 ≤ w k) ∧ (∀ k, s₀ ≤ s k) ∧
        ∀ t ∈ Icc x y, |Gfin w s t / f a t - 1| ≤ ε} (Real.tanh (D a s₀ x y / 2)) := by
  refine ⟨?_, fun ε ⟨n, w, s, hw, hs, herr⟩ =>
    tanh_le_rel_error_threshold_fin hs₀ hw hs hx hxy herr⟩
  obtain ⟨hw, hs, hall, -⟩ := one_atom_attains_fin ha hs₀ hx hxy
  exact ⟨1, _, _, fun k => (hw k).le, hs, hall⟩

/-! ### 4. Consistency with, and strengthening of, SPC-4 (`Strengthened.lean`) -/

theorem D_zero (a : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : D a 0 x y = a * (y - x) := by
  rw [D, add_zero, add_zero, show y * x / (x * y) = 1 by
    rw [mul_comm]; exact div_self (by positivity), Real.log_one, add_zero]

/-- **SPC-4 recovered.** The statement of `Strong.tanh_le_rel_error` follows from the threshold
theorem at `s₀ = 0`. -/
theorem recovers_SPC4 {ρ : Measure ℝ} (hsupp : ρ (Iio 0) = 0)
    (hint : Integrable (fun s => (1 + s)⁻¹) ρ) {a x y ε : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (herr : ∀ t ∈ Icc x y, |G ρ t / (Real.exp (-a * t) / t) - 1| ≤ ε) :
    Real.tanh (a * (y - x) / 2) ≤ ε := by
  have h := tanh_le_rel_error_threshold (a := a) le_rfl hsupp hint hx hxy herr
  rwa [D_zero a hx (by linarith)] at h

/-- At `s₀ = 0` the sharp value is the SPC-4 value `tanh(a(y-x)/2)` (cf. `Strong.rel_error_sharp`). -/
theorem sharp_threshold_zero {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 < x) (hxy : x ≤ y) :
    IsLeast {ε | ∃ ρ : Measure ℝ, ρ (Iio 0) = 0 ∧ Integrable (fun s => (1 + s)⁻¹) ρ ∧
        ∀ t ∈ Icc x y, |G ρ t / (Real.exp (-a * t) / t) - 1| ≤ ε} (Real.tanh (a * (y - x) / 2)) := by
  have h := sharp_threshold ha le_rfl hx hxy
  rwa [D_zero a hx (by linarith)] at h

lemma tanh_half_le_of_le {d₁ d₂ : ℝ} (h : d₁ ≤ d₂) : Real.tanh (d₁ / 2) ≤ Real.tanh (d₂ / 2) := by
  rw [Strong.tanh_half_eq, Strong.tanh_half_eq]
  have h1 : 0 < Real.exp (-d₁) := Real.exp_pos _
  have h2 : 0 < Real.exp (-d₂) := Real.exp_pos _
  have h3 : Real.exp (-d₂) ≤ Real.exp (-d₁) := Real.exp_le_exp.2 (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

lemma tanh_half_lt_of_lt {d₁ d₂ : ℝ} (h : d₁ < d₂) : Real.tanh (d₁ / 2) < Real.tanh (d₂ / 2) := by
  rw [Strong.tanh_half_eq, Strong.tanh_half_eq]
  have h1 : 0 < Real.exp (-d₁) := Real.exp_pos _
  have h2 : 0 < Real.exp (-d₂) := Real.exp_pos _
  have h3 : Real.exp (-d₂) < Real.exp (-d₁) := Real.exp_lt_exp.2 (by linarith)
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith

/-- **Genuine strengthening.** The threshold bound is at least the SPC-4 bound. -/
theorem strengthens_SPC4 {a s₀ x y : ℝ} (hs₀ : 0 ≤ s₀) (hx : 0 < x) (hxy : x ≤ y) :
    Real.tanh (a * (y - x) / 2) ≤ Real.tanh (D a s₀ x y / 2) := by
  refine tanh_half_le_of_le ?_
  have hy : 0 < y := by linarith
  have : 0 ≤ Real.log (y * (x + s₀) / (x * (y + s₀))) := by
    refine Real.log_nonneg ?_
    rw [one_le_div (by positivity)]; nlinarith
  rw [D]; linarith

/-- **Strict strengthening** for a positive threshold `s₀ > 0` and `x < y`. -/
theorem strengthens_SPC4_strict {a s₀ x y : ℝ} (hs₀ : 0 < s₀) (hx : 0 < x) (hxy : x < y) :
    Real.tanh (a * (y - x) / 2) < Real.tanh (D a s₀ x y / 2) := by
  refine tanh_half_lt_of_lt ?_
  have hy : 0 < y := by linarith
  have : 0 < Real.log (y * (x + s₀) / (x * (y + s₀))) := by
    refine Real.log_pos ?_
    rw [one_lt_div (by positivity)]; nlinarith
  rw [D]; linarith

end APEX.Spectral.Threshold

