import APEX.Spectral.Threshold

/-!
# Operator-valued threshold bound (finitely many PSD atoms) and the case `a < 0`

Setting (reusing `Strengthened.lean` §5): `𝕜` an `RCLike` field (`ℝ` or `ℂ`), PSD matrices
`W_k : Matrix n n 𝕜` at positions `s_k ≥ s₀ ≥ 0`, and
`Strong.Gmat s W x = ∑_k (x+s_k)⁻¹ • W_k`. Notation from `Threshold.lean`: `f a z = exp(-a z)/z`,
`D a s₀ x y = a(y-x) + log(y(x+s₀)/(x(y+s₀)))`, `φ a s₀ z = z/(z+s₀)·exp(a z)`;
`quad M v = Re (v* M v)`. Always `0 < x ≤ y`.

**Results.**
1. `loewner_threshold`: `G(y) - ((x+s₀)/(y+s₀)) • G(x)` is positive semidefinite.
2. `polarisation_threshold`: for every vector `v`, `ρ_v = ∑_k (v* W_k v) δ_{s_k}` is supported
   on `[s₀,∞)`, integrable against `(1+s)⁻¹`, and `Strong.G ρ_v = quad (G ·) v`; hence
   (`quad_threshold_mono`) `quad (G y) v ≥ (x+s₀)/(y+s₀) · quad (G x) v`, and all scalar theorems
   of `Threshold.lean` apply to `t ↦ v* G(t) v`.
3. `matrix_tanh_le_threshold`: for any real `a`, any `ε`, any matrix `P` and any `v` with
   `Re(v* P v) > 0`: if `G(x) - (1-ε) f(x) P` and `(1+ε) f(y) P - G(y)` are PSD (Loewner sandwich;
   only these two one-sided conditions are used), then `ε ≥ tanh(D/2)`.
   `matrix_tanh_le_threshold_sandwich`: the same with the full sandwich at `x` and `y`.
4. `matrix_one_atom_attains` / `matrix_sharp_threshold`: for `a ≥ 0` and PSD `P` with some
   `Re(v* P v) > 0`, the single atom `W = w P` at `s₀`, `w = 2/(φ(x)+φ(y))`, satisfies the
   Loewner sandwich with `ε = tanh(D/2)` at every `t ∈ [x,y]`, with
   `G(x) = (1 - tanh(D/2)) f(x) P` and `G(y) = (1 + tanh(D/2)) f(y) P` exactly; so
   `tanh(D/2)` is the least `ε` (`IsLeast`) for which some finite PSD-atom family on `[s₀,∞)`
   satisfies the sandwich on `[x,y]`.
5. Case `a < 0` (scalar). `tanh_le_rel_error_antitone`: any admissible `ρ` with
   `|G/f - 1| ≤ ε` on `[x,y]` has `ε ≥ tanh(D'/2)`, `D' = -a(y-x) + log(x/y)`
   (from `G` non-increasing; any real `a`, any `s₀ ≥ 0`). `not_sharp_of_lt`: whenever
   `tanh(D/2) < tanh(D'/2)`, `tanh(D/2)` is **not** the infimum of the uniform relative error
   (not `IsLeast`), and `not_sharp_example`: this happens for `a = -2`, `x = 1`, `y = 2`, `s₀ = 0`.
   So for `a < 0` the threshold value `tanh(D/2)` is in general not sharp. The exact sharp value
   for `a < 0` is **not** determined here (open); we only have the lower bound
   `max(tanh(D/2), tanh(D'/2))`.

**Physical caveat.** Necessary conditions on candidate (matrix-valued, Källén–Lehmann-type with
mass gap `s₀`) propagators only; nothing is said about non-perturbative existence or
consistency of any theory. General (non-atomic) operator-valued spectral measures are not
treated.
-/

open MeasureTheory Set Matrix
open scoped ComplexOrder

namespace APEX.Spectral.ThresholdMatrix

open APEX.Spectral.Strong (G Gmat qf rhoPol)
open APEX.Spectral.Threshold (f D φ)

variable {𝕜 : Type*} [RCLike 𝕜] {n ι : Type*} [Fintype n] [Fintype ι]

/-- Real quadratic form `Re (v* M v)`. -/
noncomputable def quad (M : Matrix n n 𝕜) (v : n → 𝕜) : ℝ := RCLike.re (star v ⬝ᵥ (M *ᵥ v))

lemma quad_nonneg {M : Matrix n n 𝕜} (hM : M.PosSemidef) (v : n → 𝕜) : 0 ≤ quad M v :=
  (RCLike.nonneg_iff.1 (hM.dotProduct_mulVec_nonneg v)).1

lemma quad_sub (A B : Matrix n n 𝕜) (v : n → 𝕜) : quad (A - B) v = quad A v - quad B v := by
  simp [quad, sub_mulVec, dotProduct_sub]

lemma quad_smul (c : ℝ) (A : Matrix n n 𝕜) (v : n → 𝕜) : quad (c • A) v = c * quad A v := by
  simp only [quad, smul_mulVec, dotProduct_smul, RCLike.smul_re]

/-! ### 1. Loewner threshold inequality -/

omit [Fintype n] in
/-- **Loewner threshold monotonicity.** -/
theorem loewner_threshold {s : ι → ℝ} {W : ι → Matrix n n 𝕜} {s₀ x y : ℝ} (hs₀ : 0 ≤ s₀)
    (hs : ∀ k, s₀ ≤ s k) (hW : ∀ k, (W k).PosSemidef) (hx : 0 < x) (hxy : x ≤ y) :
    (Gmat s W y - ((x + s₀) / (y + s₀)) • Gmat s W x).PosSemidef := by
  have : Gmat s W y - ((x + s₀) / (y + s₀)) • Gmat s W x =
      ∑ k, ((y + s k)⁻¹ - (x + s₀) / (y + s₀) * (x + s k)⁻¹) • W k := by
    simp only [Gmat, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, sub_smul]
  rw [this]
  refine posSemidef_sum _ fun k _ => (hW k).smul ?_
  exact sub_nonneg.2 (Threshold.ratio_le_inv hs₀ (hs k) hx hxy)

/-! ### 2. Polarisation -/

lemma rhoPol_supp {s : ι → ℝ} {W : ι → Matrix n n 𝕜} {s₀ : ℝ} (hs : ∀ k, s₀ ≤ s k)
    (v : n → 𝕜) : rhoPol s W v (Iio s₀) = 0 := by
  have hk : ∀ k, s k ∉ Iio s₀ := fun k => by simpa using hs k
  simp [rhoPol, Measure.dirac_apply' _ measurableSet_Iio, hk]

/-- **Polarisations satisfy the scalar threshold hypotheses.** -/
theorem polarisation_threshold {s : ι → ℝ} {W : ι → Matrix n n 𝕜} {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hs : ∀ k, s₀ ≤ s k) (hW : ∀ k, (W k).PosSemidef) (v : n → 𝕜) :
    rhoPol s W v (Iio s₀) = 0 ∧ Integrable (fun t => (1 + t)⁻¹) (rhoPol s W v) ∧
      ∀ x, G (rhoPol s W v) x = quad (Gmat s W x) v := by
  obtain ⟨-, h2, h3⟩ :=
    Strong.polarisation_is_stieltjes (fun k => hs₀.trans (hs k)) hW v
  refine ⟨rhoPol_supp hs v, h2, fun x => ?_⟩
  rw [quad, ← h3 x, RCLike.ofReal_re]

/-- Scalar threshold monotonicity of every polarisation. -/
theorem quad_threshold_mono {s : ι → ℝ} {W : ι → Matrix n n 𝕜} {s₀ x y : ℝ} (hs₀ : 0 ≤ s₀)
    (hs : ∀ k, s₀ ≤ s k) (hW : ∀ k, (W k).PosSemidef) (v : n → 𝕜) (hx : 0 < x) (hxy : x ≤ y) :
    (x + s₀) / (y + s₀) * quad (Gmat s W x) v ≤ quad (Gmat s W y) v := by
  have := quad_nonneg (loewner_threshold hs₀ hs hW hx hxy) v
  rw [quad_sub, quad_smul] at this; linarith

/-! ### 3. Loewner-sandwich lower bound -/

/-- **Matrix threshold bound.** Only the lower sandwich at `x` and the upper one at `y` are used;
any real `a`; `P` need only satisfy `Re(v* P v) > 0` for the chosen `v`. -/
theorem matrix_tanh_le_threshold {s : ι → ℝ} {W : ι → Matrix n n 𝕜} {s₀ a x y ε : ℝ}
    (hs₀ : 0 ≤ s₀) (hs : ∀ k, s₀ ≤ s k) (hW : ∀ k, (W k).PosSemidef) (hx : 0 < x) (hxy : x ≤ y)
    (P : Matrix n n 𝕜) (v : n → 𝕜) (hPv : 0 < quad P v)
    (hlo : (Gmat s W x - ((1 - ε) * f a x) • P).PosSemidef)
    (hhi : (((1 + ε) * f a y) • P - Gmat s W y).PosSemidef) :
    Real.tanh (D a s₀ x y / 2) ≤ ε := by
  set p := quad P v
  have h1 := quad_nonneg hlo v
  have h2 := quad_nonneg hhi v
  rw [quad_sub, quad_smul] at h1 h2
  refine Threshold.tanh_le_of_two_point (Gx := quad (Gmat s W x) v / p)
    (Gy := quad (Gmat s W y) v / p) hs₀ hx hxy ?_ ?_ ?_
  · rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (quad_threshold_mono hs₀ hs hW v hx hxy) hPv.le
  · rw [le_div_iff₀ hPv]; linarith
  · rw [div_le_iff₀ hPv]; linarith

/-- The full Loewner sandwich `(1-ε) f(z) P ≤ G(z) ≤ (1+ε) f(z) P` at `z = x, y`. -/
theorem matrix_tanh_le_threshold_sandwich {s : ι → ℝ} {W : ι → Matrix n n 𝕜} {s₀ a x y ε : ℝ}
    (hs₀ : 0 ≤ s₀) (hs : ∀ k, s₀ ≤ s k) (hW : ∀ k, (W k).PosSemidef) (hx : 0 < x) (hxy : x ≤ y)
    (P : Matrix n n 𝕜) (_hP : P.PosSemidef) (v : n → 𝕜) (hPv : 0 < quad P v)
    (hsand : ∀ z ∈ ({x, y} : Set ℝ), (Gmat s W z - ((1 - ε) * f a z) • P).PosSemidef ∧
      (((1 + ε) * f a z) • P - Gmat s W z).PosSemidef) :
    Real.tanh (D a s₀ x y / 2) ≤ ε :=
  matrix_tanh_le_threshold hs₀ hs hW hx hxy P v hPv (hsand x (by simp)).1 (hsand y (by simp)).2

/-! ### 4. Sharpness with the atom `w P` at `s₀` -/

omit [Fintype n] in
lemma Gmat_one_atom (w s₀ z : ℝ) (P : Matrix n n 𝕜) :
    Gmat (fun _ : Fin 1 => s₀) (fun _ => w • P) z = (w / (z + s₀)) • P := by
  simp [Gmat, smul_smul, div_eq_inv_mul]

omit [Fintype n] in
/-- **Attainability.** -/
theorem matrix_one_atom_attains {a s₀ x y : ℝ} (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀) (hx : 0 < x)
    (hxy : x ≤ y) (P : Matrix n n 𝕜) (hP : P.PosSemidef) :
    let w := 2 / (φ a s₀ x + φ a s₀ y)
    let T := Real.tanh (D a s₀ x y / 2)
    (w • P).PosSemidef ∧
      (∀ t ∈ Icc x y,
        (Gmat (fun _ : Fin 1 => s₀) (fun _ => w • P) t - ((1 - T) * f a t) • P).PosSemidef ∧
        (((1 + T) * f a t) • P - Gmat (fun _ : Fin 1 => s₀) (fun _ => w • P) t).PosSemidef) ∧
      Gmat (fun _ : Fin 1 => s₀) (fun _ => w • P) x = ((1 - T) * f a x) • P ∧
      Gmat (fun _ : Fin 1 => s₀) (fun _ => w • P) y = ((1 + T) * f a y) • P := by
  intro w T
  obtain ⟨hw, hx1, hy1, -, hall⟩ := Threshold.attain_core ha hs₀ hx hxy
  have hval : ∀ t, 0 < t → w / (t + s₀) = w * φ a s₀ t * f a t := fun t ht => by
    rw [← Threshold.one_atom_div_f a w hs₀ ht, div_mul_cancel₀ _ (Threshold.f_pos a ht).ne']
  have hy : 0 < y := by linarith
  refine ⟨hP.smul hw.le, fun t ht => ?_, ?_, ?_⟩
  · have htp : 0 < t := by linarith [ht.1]
    have hf := Threshold.f_pos a htp
    obtain ⟨h1, h2⟩ := abs_le.1 (hall t ht)
    rw [Gmat_one_atom, ← sub_smul, ← sub_smul, hval t htp]
    constructor
    · refine hP.smul ?_
      have : 0 ≤ (w * φ a s₀ t - (1 - T)) * f a t := mul_nonneg (by linarith) hf.le
      linarith
    · refine hP.smul ?_
      have : 0 ≤ ((1 + T) - w * φ a s₀ t) * f a t := mul_nonneg (by linarith) hf.le
      linarith
  · rw [Gmat_one_atom, hval x hx, hx1]
  · rw [Gmat_one_atom, hval y hy, hy1]

/-- **Sharpness (operator-valued, finite PSD atoms).** For `a ≥ 0`, `0 ≤ s₀`, `0 < x ≤ y`, a
PSD `P` and `v` with `Re(v* P v) > 0`, `tanh(D/2)` is the least `ε` such that some finite
family of PSD atoms at positions `≥ s₀` satisfies the Loewner sandwich
`(1-ε) f(t) P ≤ G(t) ≤ (1+ε) f(t) P` for all `t ∈ [x,y]`. -/
theorem matrix_sharp_threshold {a s₀ x y : ℝ} (ha : 0 ≤ a) (hs₀ : 0 ≤ s₀) (hx : 0 < x)
    (hxy : x ≤ y) (P : Matrix n n 𝕜) (hP : P.PosSemidef) (v : n → 𝕜) (hPv : 0 < quad P v) :
    IsLeast {ε | ∃ (m : ℕ) (s : Fin m → ℝ) (W : Fin m → Matrix n n 𝕜),
        (∀ k, s₀ ≤ s k) ∧ (∀ k, (W k).PosSemidef) ∧
        ∀ t ∈ Icc x y, (Gmat s W t - ((1 - ε) * f a t) • P).PosSemidef ∧
          (((1 + ε) * f a t) • P - Gmat s W t).PosSemidef}
      (Real.tanh (D a s₀ x y / 2)) := by
  refine ⟨?_, fun ε ⟨m, s, W, hs, hW, h⟩ =>
    matrix_tanh_le_threshold hs₀ hs hW hx hxy P v hPv (h x ⟨le_rfl, hxy⟩).1
      (h y ⟨hxy, le_rfl⟩).2⟩
  obtain ⟨hwP, hall, -⟩ := matrix_one_atom_attains ha hs₀ hx hxy P hP
  exact ⟨1, _, _, fun _ => le_rfl, fun _ => hwP, hall⟩

/-! ### 5. The case `a < 0`: a second lower bound, and non-sharpness of `tanh(D/2)` -/

/-- `D' = -a(y-x) + log(x/y) = log(f(y)/f(x))`. -/
noncomputable def D' (a x y : ℝ) : ℝ := -a * (y - x) + Real.log (x / y)

lemma exp_D' {a x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp (D' a x y) = f a y / f a x := by
  rw [D', Real.exp_add, Real.exp_log (by positivity), f, f]
  have h : Real.exp (-a * (y - x)) = Real.exp (-a * y) / Real.exp (-a * x) := by
    rw [← Real.exp_sub]; ring_nf
  rw [h]
  have h1 : 0 < Real.exp (-a * y) := Real.exp_pos _
  have h2 : 0 < Real.exp (-a * x) := Real.exp_pos _
  field_simp

/-- **Second lower bound** (from `G` non-increasing), any real `a`, any threshold `s₀ ≥ 0`. -/
theorem tanh_le_rel_error_antitone {ρ : Measure ℝ} {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hsupp : ρ (Iio s₀) = 0) (hint : Integrable (fun s => (1 + s)⁻¹) ρ) {a x y ε : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (herr : ∀ t ∈ Icc x y, |G ρ t / f a t - 1| ≤ ε) :
    Real.tanh (D' a x y / 2) ≤ ε := by
  have hy : 0 < y := by linarith
  have hsupp0 : ρ (Iio 0) = 0 := measure_mono_null (Iio_subset_Iio hs₀) hsupp
  have hanti : G ρ y ≤ G ρ x := Strong.antitoneOn_G hsupp0 hint hx hy hxy
  have hfx := Threshold.f_pos a hx
  have hfy := Threshold.f_pos a hy
  have hlo := (Threshold.bounds_of_abs hfy (herr y ⟨hxy, le_rfl⟩)).1
  have hhi := (Threshold.bounds_of_abs hfx (herr x ⟨le_rfl, hxy⟩)).2
  have h2 : (1 - ε) * Real.exp (D' a x y) ≤ 1 + ε := by
    rw [exp_D' hx hy, ← mul_div_assoc, div_le_iff₀ hfx]; linarith
  set q := Real.exp (-D' a x y) with hq_def
  have hq : 0 < q := Real.exp_pos _
  have hEq : Real.exp (D' a x y) * q = 1 := by rw [hq_def, ← Real.exp_add]; simp
  have h3 : 1 - ε ≤ (1 + ε) * q := by
    calc 1 - ε = (1 - ε) * Real.exp (D' a x y) * q := by rw [mul_assoc, hEq, mul_one]
      _ ≤ (1 + ε) * q := mul_le_mul_of_nonneg_right h2 hq.le
  rw [Strong.tanh_half_eq, ← hq_def, div_le_iff₀ (by linarith)]
  linarith

/-- **Non-sharpness criterion.** If `tanh(D/2) < tanh(D'/2)`, then `tanh(D/2)` is not the least
uniform relative error over admissible measures on `[s₀,∞)`. -/
theorem not_sharp_of_lt {a s₀ x y : ℝ} (hs₀ : 0 ≤ s₀) (hx : 0 < x) (hxy : x ≤ y)
    (hlt : Real.tanh (D a s₀ x y / 2) < Real.tanh (D' a x y / 2)) :
    ¬ IsLeast {ε | ∃ ρ : Measure ℝ, ρ (Iio s₀) = 0 ∧ Integrable (fun s => (1 + s)⁻¹) ρ ∧
        ∀ t ∈ Icc x y, |G ρ t / f a t - 1| ≤ ε} (Real.tanh (D a s₀ x y / 2)) := by
  rintro ⟨⟨ρ, hsupp, hint, herr⟩, -⟩
  have := tanh_le_rel_error_antitone hs₀ hsupp hint hx hxy herr
  linarith

/-- **Concrete instance** (`a = -2`, `x = 1`, `y = 2`, `s₀ = 0`): `tanh(D/2)` is not sharp. -/
theorem not_sharp_example :
    ¬ IsLeast {ε | ∃ ρ : Measure ℝ, ρ (Iio 0) = 0 ∧ Integrable (fun s => (1 + s)⁻¹) ρ ∧
        ∀ t ∈ Icc (1 : ℝ) 2, |G ρ t / f (-2) t - 1| ≤ ε} (Real.tanh (D (-2) 0 1 2 / 2)) := by
  refine not_sharp_of_lt le_rfl one_pos one_le_two ?_
  rw [Threshold.D_zero _ one_pos two_pos, D']
  have hl : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hl' : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [hl']
  exact Threshold.tanh_half_lt_of_lt (by linarith)

end APEX.Spectral.ThresholdMatrix

