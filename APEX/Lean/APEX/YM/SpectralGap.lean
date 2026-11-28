import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Hermitian

/-!
# The abstract spectral layer of the mass-gap problem

**Scope.** This file is the *abstract functional-analytic layer only*. It does **not** prove
the Yang–Mills mass gap, which remains an open problem. Everything here is standard spectral
theory: it says how a gap `Δ` in the spectrum of a Hamiltonian/transfer matrix is equivalent
to exponential decay of Euclidean correlations, and how such a gap behaves in limits. The hard
(open) analytic input for Yang–Mills is the **uniform lattice bound `λ₂(T_a) ≤ e^{-aΔ}` with
`Δ > 0` independent of the lattice spacing `a`**; here it appears only as a *hypothesis*
(`continuum_decay_of_uniform_lattice_gap`), and `fixed_gaps_not_uniform` shows that it cannot
be replaced by gaps at each fixed `a`.

## 1. Laplace-transform criterion (`corr μ t = ∫ e^{-tE} dμ(E)`, `μ` finite, `μ(Iio 0) = 0`)
* `laplace_gap_criterion`: TFAE (a) `μ(Iio m) = 0`; (b) `C(t) ≤ C(0) e^{-mt}` for `t ≥ 0`;
  (c) `∀ m' < m, ∃ K, ∀ t ≥ 0, C(t) ≤ K e^{-m't}` (components `decay_of_gap`,
  `subexp_decay_of_decay`, `gap_of_subexp_decay`). No sign condition on `m` is needed.
* `mass_below_eq_zero_of_decay`: decay at rate `r` forces `μ(Iio b) = 0` for every `b < r`
  (proof: `C(t) ≥ μ(Iio b) e^{-tb}`, `corr_ge`).
* `no_exp_decay_of_mass_near_zero`: mass in every `[0, ε)` ⇒ no exponential decay at any `m > 0`.
* `expMeasure_no_gap`: for `dμ = e^{-E} dE` on `(0,∞)`, `C(t) = 1/(1+t)` (polynomial decay),
  there is no exponential decay at any rate `m > 0`, and `μ(Iio m) ≠ 0` for all `m > 0`.

## 2. Hilbert-space version (finite-dimensional complex inner product space `E`)
* `heat A t = NormedSpace.exp (-(t) • A)` (Banach-algebra exponential in `E →L[ℂ] E`).
* `heat_gap_iff`: for `A` symmetric with `A Ω = 0`: every eigenvalue of `A` on `Ω^⊥` is `≥ m`
  iff `Re ⟪ψ, e^{-tA} ψ⟫ ≤ ‖ψ‖² e^{-mt}` for all `ψ ⊥ Ω`, `t ≥ 0`.
  ("Eigenvalue on `Ω^⊥`" = `∃ v ≠ 0, v ⊥ Ω, A v = λ v`; `Ω^⊥` is `A`-invariant.)
* `heat_inner_eq`: `⟪ψ, e^{-tA}ψ⟫ = ∑ᵢ e^{-tλᵢ} |⟪bᵢ, ψ⟫|²` in Mathlib's eigenbasis
  (`LinearMap.IsSymmetric.eigenvectorBasis`) — the finite spectral measure of `ψ`.
* `matrix_heat_gap_iff`: the same for a Hermitian matrix acting on `EuclideanSpace ℂ n`.
* Key lemma `exists_eigvec_perp`: if `ψ ⊥ Ω` has a component along the eigenvector `bᵢ`, then
  `λᵢ` is an eigenvalue of `A` on `Ω^⊥` (projection of `ψ` onto the `λᵢ`-eigenspace).

## 3. Transfer-matrix version
* `transfer_bound`: `T` symmetric, `T Ω = Ω`, spectrum on `Ω^⊥` in `[0, λ₂]` ⇒
  `Re ⟪ψ, Tⁿ ψ⟫ ≤ λ₂ⁿ ‖ψ‖²` for `ψ ⊥ Ω` (`matrix_transfer_bound` for Hermitian matrices).
* `transfer_eigen_corr`: equality `⟪v, Tⁿ v⟫ = λⁿ ‖v‖²` on eigenvectors (sharpness).
* `transfer_spectrum_le_of_bound` (some `n ≥ 1`, `q ≥ 0`, eigenvalue `≥ 0`) and
  `transfer_spectrum_le_of_bound_all` (all `n`): the bound `qⁿ‖ψ‖²` on `Ω^⊥` forces every
  eigenvalue on `Ω^⊥` to be `≤ q`.
* `transfer_physical_bound(')`: if `λ₂ ≤ e^{-aΔ}` then
  `Re ⟪ψ, T^{⌊t/a⌋} ψ⟫ ≤ e^{-Δ a ⌊t/a⌋} ‖ψ‖² ≤ e^{-Δ (t-a)} ‖ψ‖²`.

## 4. Continuum limits
* `gap_of_limit` (4a): `C_k(t) → C(t)` pointwise and a *uniform* bound
  `C_k(t) ≤ C_k(0) e^{-Δt}` ⇒ `μ(Iio Δ) = 0`.
* `nonuniform_gap_lost` (4b): `δ_{1/(k+1)}` has gap `1/(k+1)`, its correlations converge to
  those of `δ_0`, which has no gap and no exponential decay.
* `continuum_decay_of_uniform_lattice_gap` / `continuum_gap_of_uniform_lattice_gap` (4c):
  spacings `a_k → 0`, spectrum of `T_k` on `Ω_k^⊥` in `[0, e^{-a_k Δ}]` (uniform physical `Δ`),
  lattice correlations `Re ⟪ψ_k, T_k^{⌊t/a_k⌋} ψ_k⟫ → C(t)` (the continuum-limit hypothesis)
  ⇒ `C(t) ≤ C(0) e^{-Δt}`; if `C = corr μ` then `μ(Iio Δ) = 0`.
* `fixed_q_physical_rate`: a fixed bound `λ₂ ≤ q < 1` is `λ₂ ≤ e^{-aΔ_a}` with
  `Δ_a = -log q / a → ∞` as `a → 0⁺`: it says nothing about a uniform physical gap.
* `fixed_gaps_not_uniform`: `a_k = 1/(k+1)`, `λ₂(a_k) = e^{-a_k Δ_k}` with `Δ_k = a_k → 0`:
  each `λ₂(a_k) < 1`, but `λ₂(a_k)^{⌊t/a_k⌋} → 1` for every `t ≥ 0` (these are exactly the
  excited-sector correlations, `transfer_eigen_corr`), and `C ≡ 1` has no gap. So the
  uniform bound must be *assumed*; it does not follow from gaps at fixed `a`.
-/

open MeasureTheory Set Filter Topology Real

namespace APEX.YM

set_option linter.unusedSectionVars false

/-! ## 1. Laplace-transform gap criterion -/

/-- The Euclidean correlation function `C_μ(t) = ∫ exp(-t E) dμ(E)`. -/
noncomputable def corr (μ : Measure ℝ) (t : ℝ) : ℝ := ∫ E, Real.exp (-(t * E)) ∂μ

section Laplace

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

lemma ae_nonneg_of_Iio (h0 : μ (Iio 0) = 0) : ∀ᵐ E ∂μ, 0 ≤ E := by
  rw [ae_iff]; convert h0 using 2; ext; simp

lemma integrable_exp (h0 : μ (Iio 0) = 0) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun E => Real.exp (-(t * E))) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable
  · filter_upwards [ae_nonneg_of_Iio h0] with E hE
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)

lemma corr_zero : corr μ 0 = μ.real univ := by
  simp [corr]

lemma corr_nonneg (t : ℝ) : 0 ≤ corr μ t :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- Lower bound: `C(t) ≥ μ([.., b)) e^{-tb}` for `t ≥ 0`. -/
lemma corr_ge (h0 : μ (Iio 0) = 0) {t : ℝ} (ht : 0 ≤ t) (b : ℝ) :
    μ.real (Iio b) * Real.exp (-(t * b)) ≤ corr μ t := by
  have hint := integrable_exp h0 ht
  calc μ.real (Iio b) * Real.exp (-(t * b)) = ∫ _ in Iio b, Real.exp (-(t * b)) ∂μ := by
        rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ E in Iio b, Real.exp (-(t * E)) ∂μ := by
        refine setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn
          measurableSet_Iio fun E hE => Real.exp_le_exp.mpr ?_
        have : E < b := hE
        nlinarith
    _ ≤ corr μ t := setIntegral_le_integral hint (Eventually.of_forall fun _ => (Real.exp_pos _).le)

/-- Core lemma: exponential decay at rate `r` kills all spectral mass below `r`. -/
theorem mass_below_eq_zero_of_decay (h0 : μ (Iio 0) = 0) {r K : ℝ}
    (hK : ∀ t, 0 ≤ t → corr μ t ≤ K * Real.exp (-(r * t))) {b : ℝ} (hb : b < r) :
    μ (Iio b) = 0 := by
  by_contra hne
  have hpos : 0 < μ.real (Iio b) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hne (measure_ne_top _ _)
  set δ := μ.real (Iio b)
  set c := r - b
  have hc : 0 < c := by simp [c]; linarith
  set t := |K| / δ / c + 1 with ht_def
  have ht : 0 ≤ t := by positivity
  have h1 := (corr_ge h0 ht b).trans (hK t ht)
  -- δ e^{-tb} ≤ K e^{-rt}  ⇒  δ e^{ct} ≤ K
  have h2 : δ * Real.exp (c * t) ≤ K := by
    have e : Real.exp (c * t) = Real.exp (-(t * b)) / Real.exp (-(r * t)) := by
      rw [← Real.exp_sub]; congr 1; simp [c]; ring
    rw [e, ← mul_div_assoc, div_le_iff₀ (Real.exp_pos _)]
    exact h1
  have h3 : c * t + 1 ≤ Real.exp (c * t) := Real.add_one_le_exp _
  have h4 : c * t = |K| / δ + c := by
    rw [ht_def]; field_simp
  have h5 : δ * (|K| / δ + c + 1) ≤ K := by
    calc δ * (|K| / δ + c + 1) = δ * (c * t + 1) := by rw [h4]
      _ ≤ δ * Real.exp (c * t) := mul_le_mul_of_nonneg_left h3 hpos.le
      _ ≤ K := h2
  have h6 : δ * (|K| / δ + c + 1) = |K| + δ * (c + 1) := by field_simp; ring
  rw [h6] at h5
  have := le_abs_self K
  nlinarith [mul_pos hpos (by linarith : (0:ℝ) < c + 1)]

/-- (a) ⇒ (b). -/
theorem decay_of_gap (h0 : μ (Iio 0) = 0) {m : ℝ} (hm : μ (Iio m) = 0) :
    ∀ t, 0 ≤ t → corr μ t ≤ corr μ 0 * Real.exp (-(m * t)) := by
  intro t ht
  have hae : ∀ᵐ E ∂μ, m ≤ E := by rw [ae_iff]; convert hm using 2; ext; simp
  calc corr μ t ≤ ∫ _, Real.exp (-(m * t)) ∂μ := by
        refine integral_mono_ae (integrable_exp h0 ht) (integrable_const _) ?_
        filter_upwards [hae] with E hE
        exact Real.exp_le_exp.mpr (by nlinarith)
    _ = corr μ 0 * Real.exp (-(m * t)) := by
        rw [integral_const, corr_zero, smul_eq_mul]

/-- (c) ⇒ (a): decay at every rate `m' < m` implies the spectrum lies in `[m, ∞)`. -/
theorem gap_of_subexp_decay (h0 : μ (Iio 0) = 0) {m : ℝ}
    (h : ∀ m' < m, ∃ K, ∀ t, 0 ≤ t → corr μ t ≤ K * Real.exp (-(m' * t))) :
    μ (Iio m) = 0 := by
  have hU : Iio m = ⋃ n : ℕ, Iio (m - 1 / ((n : ℝ) + 1)) := by
    ext x; simp only [mem_Iio, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hU, measure_iUnion_null_iff]
  intro n
  have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨K, hK⟩ := h (m - 1 / ((n : ℝ) + 1) / 2) (by linarith)
  exact mass_below_eq_zero_of_decay h0 hK (by linarith)

/-- (b) ⇒ (c). -/
theorem subexp_decay_of_decay {m : ℝ}
    (h : ∀ t, 0 ≤ t → corr μ t ≤ corr μ 0 * Real.exp (-(m * t))) :
    ∀ m' < m, ∃ K, ∀ t, 0 ≤ t → corr μ t ≤ K * Real.exp (-(m' * t)) := by
  intro m' hm'
  refine ⟨corr μ 0, fun t ht => (h t ht).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (corr_nonneg 0)

/-- **Laplace-transform gap criterion.** For a finite positive measure `μ` on `[0, ∞)`
the following are equivalent: (a) `μ(Iio m) = 0`; (b) `C(t) ≤ C(0) e^{-mt}` for `t ≥ 0`;
(c) for every `m' < m` there is `K` with `C(t) ≤ K e^{-m't}` for `t ≥ 0`. -/
theorem laplace_gap_criterion (h0 : μ (Iio 0) = 0) (m : ℝ) :
    List.TFAE [μ (Iio m) = 0,
      ∀ t, 0 ≤ t → corr μ t ≤ corr μ 0 * Real.exp (-(m * t)),
      ∀ m' < m, ∃ K, ∀ t, 0 ≤ t → corr μ t ≤ K * Real.exp (-(m' * t))] := by
  tfae_have 1 → 2 := decay_of_gap h0
  tfae_have 2 → 3 := subexp_decay_of_decay
  tfae_have 3 → 1 := gap_of_subexp_decay h0
  tfae_finish

/-- A measure with spectral mass arbitrarily close to `0` has no exponential decay at any
positive rate. -/
theorem no_exp_decay_of_mass_near_zero (h0 : μ (Iio 0) = 0)
    (hmass : ∀ ε > 0, μ (Iio ε) ≠ 0) {m : ℝ} (hm : 0 < m) :
    ¬ ∃ K, ∀ t, 0 ≤ t → corr μ t ≤ K * Real.exp (-(m * t)) := by
  rintro ⟨K, hK⟩
  exact hmass (m / 2) (by linarith) (mass_below_eq_zero_of_decay h0 hK (by linarith))

end Laplace

/-! ### Counterexample: polynomial decay without a gap -/

/-- The measure `dμ = e^{-E} dE` on `(0, ∞)`. -/
noncomputable def expMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun E => ENNReal.ofReal (Real.exp (-E))

instance : IsFiniteMeasure expMeasure := by
  unfold expMeasure
  apply isFiniteMeasure_withDensity_ofReal
  exact (integrableOn_exp_neg_Ioi 0).hasFiniteIntegral

lemma expMeasure_Iio_zero : expMeasure (Iio 0) = 0 := by
  unfold expMeasure
  rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have : Iio (0:ℝ) ∩ Ioi 0 = ∅ := by ext x; simp; intro h; linarith
  simp [this]

lemma corr_expMeasure {t : ℝ} (ht : 0 ≤ t) : corr expMeasure t = 1 / (1 + t) := by
  unfold corr expMeasure
  have hf : Measurable fun E : ℝ => (Real.exp (-E)).toNNReal :=
    (Real.continuous_exp.comp continuous_neg).measurable.real_toNNReal
  have := integral_withDensity_eq_integral_smul (μ := volume.restrict (Ioi 0)) hf
    (fun E => Real.exp (-(t * E)))
  simp only [ENNReal.ofReal] at this ⊢
  rw [this]
  have h2 : ∀ E : ℝ, (Real.exp (-E)).toNNReal • Real.exp (-(t * E)) =
      Real.exp ((-(1 + t)) * E) := by
    intro E
    rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, smul_eq_mul, ← Real.exp_add]
    congr 1; ring
  simp_rw [h2]
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  rw [div_neg, neg_div, neg_neg]

/-- `e^{-E} dE` has polynomial decay `C(t) = 1/(1+t)`, no exponential decay at any rate
`m > 0`, and (equivalently, by the criterion) no spectral gap. -/
theorem expMeasure_no_gap :
    (∀ t, 0 ≤ t → corr expMeasure t = 1 / (1 + t)) ∧
    (∀ m > 0, ¬ ∃ K, ∀ t, 0 ≤ t → corr expMeasure t ≤ K * Real.exp (-(m * t))) ∧
    (∀ m > 0, expMeasure (Iio m) ≠ 0) := by
  have hnd : ∀ m > 0, ¬ ∃ K, ∀ t, 0 ≤ t → corr expMeasure t ≤ K * Real.exp (-(m * t)) := by
    rintro m hm ⟨K, hK⟩
    set t : ℝ := 4 * |K| / m ^ 2 + 1 with ht_def
    have ht1 : 1 ≤ t := by have : 0 ≤ 4 * |K| / m ^ 2 := by positivity
                           linarith
    have h1 := hK t (by linarith)
    rw [corr_expMeasure (by linarith)] at h1
    have he : (m * t) ^ 2 / 2 ≤ Real.exp (m * t) := by
      have := Real.pow_div_factorial_le_exp (x := m * t) (by positivity) 2
      simpa using this
    have hepos := Real.exp_pos (m * t)
    -- 1/(1+t) ≤ K e^{-mt}  ⇒  e^{mt} ≤ K (1+t)
    have h2 : Real.exp (m * t) ≤ K * (1 + t) := by
      rw [Real.exp_neg] at h1
      rw [div_le_iff₀ (by linarith), mul_comm, ← mul_assoc, ← div_eq_mul_inv,
        le_div_iff₀ hepos] at h1
      linarith
    have hmt : m ^ 2 * t = 4 * |K| + m ^ 2 := by
      rw [ht_def]; field_simp
    have hK1 : K * (1 + t) ≤ |K| * (2 * t) := by
      have := le_abs_self K
      nlinarith [abs_nonneg K]
    -- (m t)^2 / 2 = t (4|K| + m^2)/2 > 2 |K| t
    have : (m * t) ^ 2 / 2 = t * (4 * |K| + m ^ 2) / 2 := by rw [← hmt]; ring
    nlinarith [sq_nonneg m, mul_pos hm hm]
  refine ⟨fun t ht => corr_expMeasure ht, hnd, fun m hm h => hnd m hm ⟨corr expMeasure 0, ?_⟩⟩
  exact decay_of_gap expMeasure_Iio_zero h

/-! ## Finite-dimensional operator layer -/

open scoped InnerProductSpace
open Module

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- If `F` acts diagonally on an orthonormal basis, `⟪ψ, F ψ⟫ = ∑ f_i |⟪b_i, ψ⟫|²`. -/
lemma inner_diag {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (F : E →ₗ[ℂ] E)
    (f : ι → ℝ) (hF : ∀ i, F (b i) = (f i : ℂ) • b i) (ψ : E) :
    ⟪ψ, F ψ⟫_ℂ = ((∑ i, f i * ‖⟪b i, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  have hψ : F ψ = ∑ i, ⟪b i, ψ⟫_ℂ • (f i : ℂ) • b i := by
    conv_lhs => rw [← b.sum_repr' ψ]
    simp only [map_sum, map_smul, hF]
  rw [hψ, inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, inner_smul_right, ← inner_conj_symm ψ (b i), mul_left_comm,
    RCLike.mul_conj]
  norm_cast
  exact (Complex.ofReal_mul _ _).symm

lemma re_inner_diag_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (F : E →ₗ[ℂ] E)
    (f : ι → ℝ) (hF : ∀ i, F (b i) = (f i : ℂ) • b i) (ψ : E) (B : ℝ)
    (hB : ∀ i, ⟪b i, ψ⟫_ℂ ≠ 0 → f i ≤ B) :
    RCLike.re ⟪ψ, F ψ⟫_ℂ ≤ B * ‖ψ‖ ^ 2 := by
  rw [inner_diag b F f hF, ← b.sum_sq_norm_inner_right ψ, Finset.mul_sum]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : ⟪b i, ψ⟫_ℂ = 0
  · simp [h]
  · exact mul_le_mul_of_nonneg_right (hB i h) (by positivity)

lemma inner_eigen (F : E →ₗ[ℂ] E) {v : E} {c : ℂ} (hv : F v = c • v) :
    ⟪v, F v⟫_ℂ = c * (‖v‖ : ℂ) ^ 2 := by
  rw [hv, inner_smul_right, inner_self_eq_norm_sq_to_K]
  rfl

/-- **Spectral support lemma.** Let `T` be symmetric with eigenvector `Ω` (eigenvalue `θ`),
`b` an orthonormal eigenbasis of `T` (`T b_j = λ_j b_j`), `ψ ⊥ Ω`, and suppose `ψ` has a
nonzero component along `b_i`. Then `λ_i` is an eigenvalue of `T` restricted to `Ω^⊥`
(witnessed by the projection of `ψ` onto the `λ_i`-eigenspace). -/
lemma exists_eigvec_perp {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (hb : ∀ j, T (b j) = (lam j : ℂ) • b j)
    {Ω : E} {θ : ℝ} (hΩ : T Ω = (θ : ℂ) • Ω) {ψ : E} (hψ : ⟪Ω, ψ⟫_ℂ = 0) (i : ι)
    (hi : ⟪b i, ψ⟫_ℂ ≠ 0) :
    ∃ v : E, v ≠ 0 ∧ ⟪Ω, v⟫_ℂ = 0 ∧ T v = (lam i : ℂ) • v := by
  classical
  refine ⟨∑ j ∈ Finset.univ.filter (fun j => lam j = lam i), ⟪b j, ψ⟫_ℂ • b j, ?_, ?_, ?_⟩
  · intro h0
    apply hi
    have := congrArg (fun w => ⟪b i, w⟫_ℂ) h0
    simp only [inner_sum, inner_smul_right, b.inner_eq_ite, inner_zero_right] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (by simp : i ∈ Finset.univ.filter (fun j => lam j = lam i)) h
  · -- `⟪Ω, b_j⟫ = 0` unless `λ_j = θ`
    have key : ∀ j, lam j ≠ θ → ⟪Ω, b j⟫_ℂ = 0 := by
      intro j hj
      have h1 : ⟪T Ω, b j⟫_ℂ = ⟪Ω, T (b j)⟫_ℂ := hT Ω (b j)
      rw [hΩ, hb, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
      have : ((θ : ℂ) - lam j) * ⟪Ω, b j⟫_ℂ = 0 := by rw [sub_mul, h1]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by exact_mod_cast (sub_eq_zero.mp h).symm) hj
      · exact h
    rw [inner_sum]
    simp only [inner_smul_right]
    by_cases hθ : lam i = θ
    · rw [← hψ, ← b.sum_inner_mul_inner Ω ψ, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · ring
      · rw [key j (by rwa [← hθ]), zero_mul]
    · refine Finset.sum_eq_zero fun j hj => ?_
      have hj' : lam j = lam i := (Finset.mem_filter.mp hj).2
      rw [key j (by rw [hj']; exact hθ), mul_zero]
  · rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_smul, hb, (Finset.mem_filter.mp hj).2, smul_comm]

/-- Generic bound: if `F` is diagonal in the eigenbasis of `T` with `F b_i = f(λ_i) b_i` and
`f(λ) ≤ B` for every eigenvalue `λ` of `T` on `Ω^⊥`, then `Re ⟪ψ, F ψ⟫ ≤ B ‖ψ‖²` on `Ω^⊥`. -/
lemma re_inner_le_of_perp_spectrum {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : finrank ℂ E = n) {Ω : E} {θ : ℝ} (hΩ : T Ω = (θ : ℂ) • Ω) (F : E →ₗ[ℂ] E)
    (f : ℝ → ℝ) (hF : ∀ i, F (hT.eigenvectorBasis hn i) =
      (f (hT.eigenvalues hn i) : ℂ) • hT.eigenvectorBasis hn i) (B : ℝ)
    (hB : ∀ (v : E) (lam : ℝ), v ≠ 0 → ⟪Ω, v⟫_ℂ = 0 → T v = (lam : ℂ) • v → f lam ≤ B)
    {ψ : E} (hψ : ⟪Ω, ψ⟫_ℂ = 0) :
    RCLike.re ⟪ψ, F ψ⟫_ℂ ≤ B * ‖ψ‖ ^ 2 := by
  refine re_inner_diag_le (hT.eigenvectorBasis hn) F (fun i => f (hT.eigenvalues hn i)) hF ψ B ?_
  intro i hi
  obtain ⟨v, hv0, hvΩ, hv⟩ := exists_eigvec_perp hT (hT.eigenvectorBasis hn) (hT.eigenvalues hn)
    (hT.apply_eigenvectorBasis hn) hΩ hψ i hi
  exact hB v _ hv0 hvΩ hv

/-! ### Heat semigroup `e^{-tA}` -/

/-- The Euclidean heat semigroup `e^{-tA}` (Banach-algebra exponential in `E →L[ℂ] E`). -/
noncomputable def heat (A : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E := NormedSpace.exp ((-(t : ℂ)) • A)

lemma pow_apply_eigen (A : E →L[ℂ] E) {v : E} {c : ℂ} (hv : A v = c • v) (k : ℕ) :
    (A ^ k) v = c ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    show (A ^ k) (A v) = _
    rw [hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

/-- On an eigenvector, `exp(A) v = e^{c} v`. -/
lemma exp_apply_eigen (A : E →L[ℂ] E) {v : E} {c : ℂ} (hv : A v = c • v) :
    NormedSpace.exp A v = Complex.exp c • v := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
  have h1 := (ContinuousLinearMap.apply ℂ E v).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const v
  simp only [ContinuousLinearMap.apply_apply, smul_apply,
    pow_apply_eigen A hv, smul_smul] at h1
  simp only [smul_eq_mul] at h2
  rw [Complex.exp_eq_exp_ℂ]
  exact h1.unique h2

lemma heat_apply_eigen (A : E →L[ℂ] E) {v : E} {lam : ℝ} (hv : A v = (lam : ℂ) • v) (t : ℝ) :
    heat A t v = (Real.exp (-(t * lam)) : ℂ) • v := by
  unfold heat
  rw [exp_apply_eigen _ (c := -(t : ℂ) * lam)]
  · rw [show (-(t:ℂ)) * lam = ((-(t * lam) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  · rw [smul_apply, hv, smul_smul]

/-- **Hilbert-space gap criterion.** `A` symmetric with ground state `Ω` (`A Ω = 0`).
Every eigenvalue of `A` on `Ω^⊥` is `≥ m` iff `Re ⟪ψ, e^{-tA} ψ⟫ ≤ ‖ψ‖² e^{-mt}`
for all `ψ ⊥ Ω` and `t ≥ 0`. -/
theorem heat_gap_iff (A : E →L[ℂ] E) (hA : (A : E →ₗ[ℂ] E).IsSymmetric) {Ω : E}
    (hΩ : A Ω = 0) (m : ℝ) :
    (∀ (v : E) (lam : ℝ), v ≠ 0 → ⟪Ω, v⟫_ℂ = 0 → A v = (lam : ℂ) • v → m ≤ lam) ↔
    (∀ ψ : E, ⟪Ω, ψ⟫_ℂ = 0 → ∀ t : ℝ, 0 ≤ t →
      RCLike.re ⟪ψ, heat A t ψ⟫_ℂ ≤ ‖ψ‖ ^ 2 * Real.exp (-(m * t))) := by
  constructor
  · intro hgap ψ hψ t ht
    have hΩ' : (A : E →ₗ[ℂ] E) Ω = ((0:ℝ) : ℂ) • Ω := by simp [hΩ]
    have := re_inner_le_of_perp_spectrum hA rfl hΩ' (heat A t : E →ₗ[ℂ] E)
      (fun lam => Real.exp (-(t * lam)))
      (fun i => heat_apply_eigen A (hA.apply_eigenvectorBasis rfl i) t)
      (Real.exp (-(m * t)))
      (fun v lam hv0 hvΩ hv => Real.exp_le_exp.mpr (by nlinarith [hgap v lam hv0 hvΩ hv])) hψ
    simpa [mul_comm] using this
  · intro hdec v lam hv0 hvΩ hv
    have h1 := hdec v hvΩ 1 zero_le_one
    rw [show ⟪v, heat A 1 v⟫_ℂ = ⟪v, (heat A 1 : E →ₗ[ℂ] E) v⟫_ℂ from rfl,
      inner_eigen _ (heat_apply_eigen A hv 1)] at h1
    have h2 : RCLike.re ((Real.exp (-(1 * lam)) : ℂ) * (‖v‖ : ℂ) ^ 2) =
        Real.exp (-(1 * lam)) * ‖v‖ ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]; rfl
    rw [h2] at h1
    have hv2 : 0 < ‖v‖ ^ 2 := by positivity
    have : Real.exp (-(1 * lam)) ≤ Real.exp (-(m * 1)) := by nlinarith
    have := Real.exp_le_exp.mp this
    linarith

/-- Explicit spectral representation `⟪ψ, e^{-tA} ψ⟫ = ∑ e^{-tλ_i} |⟪b_i, ψ⟫|²`
(in particular it is real). -/
theorem heat_inner_eq (A : E →L[ℂ] E) (hA : (A : E →ₗ[ℂ] E).IsSymmetric) {n : ℕ}
    (hn : finrank ℂ E = n) (t : ℝ) (ψ : E) :
    ⟪ψ, heat A t ψ⟫_ℂ = ((∑ i, Real.exp (-(t * hA.eigenvalues hn i)) *
      ‖⟪hA.eigenvectorBasis hn i, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) :=
  inner_diag (hA.eigenvectorBasis hn) (heat A t : E →ₗ[ℂ] E) _
    (fun i => heat_apply_eigen A (hA.apply_eigenvectorBasis hn i) t) ψ

/-! ### Transfer matrix `T` -/

lemma linpow_apply_eigen (T : E →ₗ[ℂ] E) {v : E} {c : ℂ} (hv : T v = c • v) (k : ℕ) :
    (T ^ k) v = c ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_apply_eq_comp, hv, map_smul, ih, smul_smul,
      pow_succ, mul_comm]

/-- **Transfer-matrix bound.** `T` symmetric, `T Ω = Ω`, every eigenvalue of `T` on `Ω^⊥`
in `[0, λ₂]`. Then `Re ⟪ψ, T^n ψ⟫ ≤ λ₂^n ‖ψ‖²` for `ψ ⊥ Ω`. -/
theorem transfer_bound {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {Ω : E} (hΩ : T Ω = Ω)
    {lam₂ : ℝ}
    (hspec : ∀ (v : E) (lam : ℝ), v ≠ 0 → ⟪Ω, v⟫_ℂ = 0 → T v = (lam : ℂ) • v →
      0 ≤ lam ∧ lam ≤ lam₂)
    {ψ : E} (hψ : ⟪Ω, ψ⟫_ℂ = 0) (n : ℕ) :
    RCLike.re ⟪ψ, (T ^ n) ψ⟫_ℂ ≤ lam₂ ^ n * ‖ψ‖ ^ 2 := by
  have hΩ' : T Ω = ((1:ℝ) : ℂ) • Ω := by simp [hΩ]
  refine re_inner_le_of_perp_spectrum hT rfl hΩ' (T ^ n) (fun lam => lam ^ n) ?_ _ ?_ hψ
  · intro i
    rw [linpow_apply_eigen T (hT.apply_eigenvectorBasis rfl i)]
    push_cast; rfl
  · intro v lam hv0 hvΩ hv
    obtain ⟨h0, h1⟩ := hspec v lam hv0 hvΩ hv
    exact pow_le_pow_left₀ h0 h1 n

/-- Exact value on an excited eigenvector: `⟪v, T^n v⟫ = λ^n ‖v‖²` (the bound is sharp). -/
theorem transfer_eigen_corr (T : E →ₗ[ℂ] E) {v : E} {lam : ℝ} (hv : T v = (lam : ℂ) • v)
    (n : ℕ) : RCLike.re ⟪v, (T ^ n) v⟫_ℂ = lam ^ n * ‖v‖ ^ 2 := by
  have : ((lam : ℂ)) ^ n * (‖v‖ : ℂ) ^ 2 = ((lam ^ n * ‖v‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [inner_eigen _ (linpow_apply_eigen T hv n), this]
  exact Complex.ofReal_re _

/-- **Converse.** If for some `n ≥ 1`, `Re ⟪ψ, T^n ψ⟫ ≤ q^n ‖ψ‖²` for all `ψ ⊥ Ω`
(with `q ≥ 0`), then every nonnegative eigenvalue of `T` on `Ω^⊥` is `≤ q`. -/
theorem transfer_spectrum_le_of_bound (T : E →ₗ[ℂ] E) {Ω : E} {q : ℝ} (hq : 0 ≤ q) {n : ℕ}
    (hn : n ≠ 0)
    (hbd : ∀ ψ : E, ⟪Ω, ψ⟫_ℂ = 0 → RCLike.re ⟪ψ, (T ^ n) ψ⟫_ℂ ≤ q ^ n * ‖ψ‖ ^ 2)
    (v : E) (lam : ℝ) (hv0 : v ≠ 0) (hvΩ : ⟪Ω, v⟫_ℂ = 0) (hv : T v = (lam : ℂ) • v)
    (hlam : 0 ≤ lam) : lam ≤ q := by
  have h := hbd v hvΩ
  rw [transfer_eigen_corr T hv n] at h
  have hv2 : 0 < ‖v‖ ^ 2 := by positivity
  have : lam ^ n ≤ q ^ n := le_of_mul_le_mul_right h hv2
  exact (pow_le_pow_iff_left₀ hlam hq hn).mp this

/-- Version with all `n`: every eigenvalue (of any sign) on `Ω^⊥` is `≤ q`. -/
theorem transfer_spectrum_le_of_bound_all (T : E →ₗ[ℂ] E) {Ω : E} {q : ℝ}
    (hbd : ∀ ψ : E, ⟪Ω, ψ⟫_ℂ = 0 → ∀ n : ℕ, RCLike.re ⟪ψ, (T ^ n) ψ⟫_ℂ ≤ q ^ n * ‖ψ‖ ^ 2)
    (v : E) (lam : ℝ) (hv0 : v ≠ 0) (hvΩ : ⟪Ω, v⟫_ℂ = 0) (hv : T v = (lam : ℂ) • v) :
    lam ≤ q := by
  have h := hbd v hvΩ 1
  rw [transfer_eigen_corr T hv 1] at h
  have hv2 : 0 < ‖v‖ ^ 2 := by positivity
  simpa using le_of_mul_le_mul_right h hv2

/-- **Physical units.** If `λ₂ ≤ e^{-aΔ}` then
`Re ⟪ψ, T^{⌊t/a⌋} ψ⟫ ≤ e^{-Δ · a⌊t/a⌋} ‖ψ‖²`, and for `Δ ≥ 0`, `a > 0`, `t ≥ 0` this is
`≤ e^{-Δ (t - a)} ‖ψ‖²`. -/
theorem transfer_physical_bound {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {Ω : E} (hΩ : T Ω = Ω)
    {a Δ : ℝ}
    (hspec : ∀ (v : E) (lam : ℝ), v ≠ 0 → ⟪Ω, v⟫_ℂ = 0 → T v = (lam : ℂ) • v →
      0 ≤ lam ∧ lam ≤ Real.exp (-(a * Δ)))
    {ψ : E} (hψ : ⟪Ω, ψ⟫_ℂ = 0) (t : ℝ) :
    RCLike.re ⟪ψ, (T ^ ⌊t / a⌋₊) ψ⟫_ℂ ≤ Real.exp (-(Δ * (a * ⌊t / a⌋₊))) * ‖ψ‖ ^ 2 := by
  have h := transfer_bound hT hΩ hspec hψ ⌊t / a⌋₊
  rw [← Real.exp_nat_mul] at h
  convert h using 3; ring

lemma floor_mul_bounds {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    t - a ≤ a * ⌊t / a⌋₊ ∧ a * ⌊t / a⌋₊ ≤ t := by
  constructor
  · have := Nat.lt_floor_add_one (t / a)
    have h2 : t = a * (t / a) := by field_simp
    nlinarith
  · have := Nat.floor_le (div_nonneg ht ha.le)
    calc a * ⌊t / a⌋₊ ≤ a * (t / a) := mul_le_mul_of_nonneg_left this ha.le
      _ = t := by field_simp

theorem transfer_physical_bound' {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {Ω : E} (hΩ : T Ω = Ω)
    {a Δ : ℝ} (ha : 0 < a) (hΔ : 0 ≤ Δ)
    (hspec : ∀ (v : E) (lam : ℝ), v ≠ 0 → ⟪Ω, v⟫_ℂ = 0 → T v = (lam : ℂ) • v →
      0 ≤ lam ∧ lam ≤ Real.exp (-(a * Δ)))
    {ψ : E} (hψ : ⟪Ω, ψ⟫_ℂ = 0) {t : ℝ} (ht : 0 ≤ t) :
    RCLike.re ⟪ψ, (T ^ ⌊t / a⌋₊) ψ⟫_ℂ ≤ Real.exp (-(Δ * (t - a))) * ‖ψ‖ ^ 2 := by
  refine (transfer_physical_bound hT hΩ hspec hψ t).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity))
  have := (floor_mul_bounds ha ht).1
  nlinarith

end Operator

/-! ### Matrix corollaries (`EuclideanSpace ℂ n`) -/

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Transfer-matrix bound for a Hermitian matrix `M` (acting on `EuclideanSpace ℂ n`). -/
theorem matrix_transfer_bound {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {Ω : EuclideanSpace ℂ n} (hΩ : M.toEuclideanLin Ω = Ω) {lam₂ : ℝ}
    (hspec : ∀ (v : EuclideanSpace ℂ n) (lam : ℝ), v ≠ 0 → ⟪Ω, v⟫_ℂ = 0 →
      M.toEuclideanLin v = (lam : ℂ) • v → 0 ≤ lam ∧ lam ≤ lam₂)
    {ψ : EuclideanSpace ℂ n} (hψ : ⟪Ω, ψ⟫_ℂ = 0) (k : ℕ) :
    RCLike.re ⟪ψ, (M.toEuclideanLin ^ k) ψ⟫_ℂ ≤ lam₂ ^ k * ‖ψ‖ ^ 2 :=
  transfer_bound (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM) hΩ hspec hψ k

/-- Heat-semigroup gap criterion for a Hermitian matrix `M` with `M Ω = 0`. -/
theorem matrix_heat_gap_iff {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {Ω : EuclideanSpace ℂ n} (hΩ : M.toEuclideanLin Ω = 0) (m : ℝ) :
    (∀ (v : EuclideanSpace ℂ n) (lam : ℝ), v ≠ 0 → ⟪Ω, v⟫_ℂ = 0 →
      M.toEuclideanLin v = (lam : ℂ) • v → m ≤ lam) ↔
    (∀ ψ : EuclideanSpace ℂ n, ⟪Ω, ψ⟫_ℂ = 0 → ∀ t : ℝ, 0 ≤ t →
      RCLike.re ⟪ψ, heat (LinearMap.toContinuousLinearMap M.toEuclideanLin) t ψ⟫_ℂ ≤
        ‖ψ‖ ^ 2 * Real.exp (-(m * t))) :=
  heat_gap_iff (LinearMap.toContinuousLinearMap M.toEuclideanLin)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM) hΩ m

end Matrix

/-! ## 4. Continuum limit: preservation of uniform gaps and loss of non-uniform ones -/

/-- **(4a) Uniform gaps survive limits.** -/
theorem gap_of_limit {μs : ℕ → Measure ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h0 : μ (Iio 0) = 0)
    (hlim : ∀ t, 0 ≤ t → Tendsto (fun k => corr (μs k) t) atTop (𝓝 (corr μ t))) {Δ : ℝ}
    (hgap : ∀ k t, 0 ≤ t → corr (μs k) t ≤ corr (μs k) 0 * Real.exp (-(Δ * t))) :
    μ (Iio Δ) = 0 := by
  have hdec : ∀ t, 0 ≤ t → corr μ t ≤ corr μ 0 * Real.exp (-(Δ * t)) := fun t ht =>
    le_of_tendsto_of_tendsto' (hlim t ht) ((hlim 0 le_rfl).mul_const _) fun k => hgap k t ht
  exact gap_of_subexp_decay h0 (subexp_decay_of_decay hdec)

lemma corr_dirac (a t : ℝ) : corr (Measure.dirac a) t = Real.exp (-(t * a)) := by
  simp [corr, integral_dirac]

/-- **(4b) Non-uniform gaps are lost.** `δ_{1/(k+1)}` has gap `1/(k+1)`, the correlations
converge to those of `δ_0`, which has no gap and no exponential decay at any rate. -/
theorem nonuniform_gap_lost :
    (∀ k : ℕ, Measure.dirac (1 / ((k : ℝ) + 1)) (Iio (1 / ((k : ℝ) + 1))) = 0) ∧
    (∀ t : ℝ, Tendsto (fun k : ℕ => corr (Measure.dirac (1 / ((k : ℝ) + 1))) t) atTop
      (𝓝 (corr (Measure.dirac 0) t))) ∧
    (∀ m > 0, Measure.dirac (0 : ℝ) (Iio m) ≠ 0) ∧
    (∀ m > 0, ¬ ∃ K, ∀ t, 0 ≤ t → corr (Measure.dirac 0) t ≤ K * Real.exp (-(m * t))) := by
  have hmass : ∀ m > 0, Measure.dirac (0 : ℝ) (Iio m) ≠ 0 := by
    intro m hm; rw [Measure.dirac_apply_of_mem (show (0:ℝ) ∈ Iio m from hm)]; simp
  refine ⟨fun k => ?_, fun t => ?_, hmass, fun m hm => ?_⟩
  · rw [Measure.dirac_apply' _ measurableSet_Iio]; simp
  · simp only [corr_dirac]
    have hc : Continuous fun x : ℝ => Real.exp (-(t * x)) := by fun_prop
    exact (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · exact no_exp_decay_of_mass_near_zero (by simp [Measure.dirac_apply' _ measurableSet_Iio])
      hmass hm

section Lattice

variable {F : ℕ → Type*} [∀ k, NormedAddCommGroup (F k)] [∀ k, InnerProductSpace ℂ (F k)]
  [∀ k, FiniteDimensional ℂ (F k)]

lemma tendsto_floor_mul {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0)) {t : ℝ}
    (ht : 0 ≤ t) : Tendsto (fun k => a k * ⌊t / a k⌋₊) atTop (𝓝 t) := by
  have hlow : Tendsto (fun k => t - a k) atTop (𝓝 t) := by simpa using tendsto_const_nhds.sub ha0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun k => (floor_mul_bounds (ha k) ht).1) (fun k => (floor_mul_bounds (ha k) ht).2)

/-- **(4c) Lattice continuum limit with a uniform physical gap.** Spacings `a_k → 0`,
transfer matrices `T_k` with `T_k Ω_k = Ω_k` and spectrum on `Ω_k^⊥` in `[0, e^{-a_k Δ}]`
(the same physical `Δ` for all `k`), vectors `ψ_k ⊥ Ω_k`, and lattice correlations
`Re ⟪ψ_k, T_k^{⌊t/a_k⌋} ψ_k⟫ → C(t)`. Then `C(t) ≤ C(0) e^{-Δt}`. -/
theorem continuum_decay_of_uniform_lattice_gap (a : ℕ → ℝ) (ha : ∀ k, 0 < a k)
    (ha0 : Tendsto a atTop (𝓝 0)) (T : ∀ k, F k →ₗ[ℂ] F k) (hT : ∀ k, (T k).IsSymmetric)
    (Ω : ∀ k, F k) (hΩ : ∀ k, T k (Ω k) = Ω k) {Δ : ℝ}
    (hgap : ∀ k (v : F k) (lam : ℝ), v ≠ 0 → ⟪Ω k, v⟫_ℂ = 0 → T k v = (lam : ℂ) • v →
      0 ≤ lam ∧ lam ≤ Real.exp (-(a k * Δ)))
    (ψ : ∀ k, F k) (hψ : ∀ k, ⟪Ω k, ψ k⟫_ℂ = 0) (C : ℝ → ℝ)
    (hC : ∀ t, 0 ≤ t → Tendsto (fun k => RCLike.re ⟪ψ k, (T k ^ ⌊t / a k⌋₊) (ψ k)⟫_ℂ) atTop
      (𝓝 (C t))) :
    ∀ t, 0 ≤ t → C t ≤ C 0 * Real.exp (-(Δ * t)) := by
  intro t ht
  have hnorm : Tendsto (fun k => ‖ψ k‖ ^ 2) atTop (𝓝 (C 0)) := by
    have := hC 0 le_rfl
    simp only [zero_div, Nat.floor_zero, pow_zero, one_apply_eq_self] at this
    refine this.congr fun k => ?_
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hexp : Tendsto (fun k => Real.exp (-(Δ * (a k * ⌊t / a k⌋₊)))) atTop
      (𝓝 (Real.exp (-(Δ * t)))) := by
    have hc : Continuous fun x : ℝ => Real.exp (-(Δ * x)) := by fun_prop
    exact (hc.tendsto t).comp (tendsto_floor_mul ha ha0 ht)
  have := le_of_tendsto_of_tendsto' (hC t ht) (hexp.mul hnorm)
    fun k => transfer_physical_bound (hT k) (hΩ k) (hgap k) (hψ k) t
  linarith [mul_comm (Real.exp (-(Δ * t))) (C 0)]

/-- Corollary: if the limit `C` is the Laplace transform of a finite spectral measure on
`[0,∞)`, that measure has no mass below `Δ`. -/
theorem continuum_gap_of_uniform_lattice_gap (a : ℕ → ℝ) (ha : ∀ k, 0 < a k)
    (ha0 : Tendsto a atTop (𝓝 0)) (T : ∀ k, F k →ₗ[ℂ] F k) (hT : ∀ k, (T k).IsSymmetric)
    (Ω : ∀ k, F k) (hΩ : ∀ k, T k (Ω k) = Ω k) {Δ : ℝ}
    (hgap : ∀ k (v : F k) (lam : ℝ), v ≠ 0 → ⟪Ω k, v⟫_ℂ = 0 → T k v = (lam : ℂ) • v →
      0 ≤ lam ∧ lam ≤ Real.exp (-(a k * Δ)))
    (ψ : ∀ k, F k) (hψ : ∀ k, ⟪Ω k, ψ k⟫_ℂ = 0) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h0 : μ (Iio 0) = 0)
    (hC : ∀ t, 0 ≤ t → Tendsto (fun k => RCLike.re ⟪ψ k, (T k ^ ⌊t / a k⌋₊) (ψ k)⟫_ℂ) atTop
      (𝓝 (corr μ t))) :
    μ (Iio Δ) = 0 :=
  gap_of_subexp_decay h0 (subexp_decay_of_decay
    (continuum_decay_of_uniform_lattice_gap a ha ha0 T hT Ω hΩ hgap ψ hψ _ hC))

end Lattice

/-- **Fixed-`a` gaps in physical units.** A bound `λ₂ ≤ q` with `q ∈ (0,1)` independent of
`a` is the statement `λ₂ ≤ e^{-a Δ_a}` with `Δ_a = -log q / a`, and `Δ_a → ∞` as `a → 0⁺`.
So a fixed-`q` gap is not the relevant (uniform) statement. -/
theorem fixed_q_physical_rate {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (∀ a : ℝ, 0 < a → q = Real.exp (-(a * (-Real.log q / a)))) ∧
    Tendsto (fun a : ℝ => -Real.log q / a) (𝓝[>] 0) atTop := by
  refine ⟨fun a ha => ?_, ?_⟩
  · rw [show a * (-Real.log q / a) = -Real.log q by field_simp, neg_neg, Real.exp_log hq0]
  · have hlog : 0 < -Real.log q := by linarith [Real.log_neg hq0 hq1]
    exact tendsto_inv_nhdsGT_zero.const_mul_atTop hlog |>.congr fun a => by ring

/-- **A family with fixed-`a` gaps but no uniform physical gap.** With `a_k = 1/(k+1)` and
`λ₂(a_k) = e^{-a_k Δ_k}`, `Δ_k = a_k → 0`: each `λ₂(a_k) < 1`, yet the excited-sector
correlation `λ₂(a_k)^{⌊t/a_k⌋}` (exact value, see `transfer_eigen_corr`) tends to `1` for
every `t ≥ 0`, so the limit `C ≡ 1` obeys no bound `C(t) ≤ C(0) e^{-Δt}` with `Δ > 0`. -/
theorem fixed_gaps_not_uniform :
    let a : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    let lam₂ : ℕ → ℝ := fun k => Real.exp (-(a k * a k))
    (∀ k, 0 < lam₂ k ∧ lam₂ k < 1) ∧
    Tendsto a atTop (𝓝 0) ∧
    (∀ t, 0 ≤ t → Tendsto (fun k => lam₂ k ^ ⌊t / a k⌋₊) atTop (𝓝 1)) ∧
    (∀ Δ > 0, ¬ ∀ t, 0 ≤ t → (1 : ℝ) ≤ 1 * Real.exp (-(Δ * t))) := by
  intro a lam₂
  have ha : ∀ k, 0 < a k := fun k => by simp only [a]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun k => ⟨Real.exp_pos _, ?_⟩, ha0, fun t ht => ?_, fun Δ hΔ h => ?_⟩
  · simp only [lam₂, Real.exp_lt_one_iff, neg_lt_zero]; exact mul_pos (ha k) (ha k)
  · have e : ∀ k, lam₂ k ^ ⌊t / a k⌋₊ = Real.exp (-(a k * (a k * ⌊t / a k⌋₊))) := by
      intro k; simp only [lam₂]; rw [← Real.exp_nat_mul]; ring_nf
    simp_rw [e]
    have h2 : Tendsto (fun k => a k * (a k * ⌊t / a k⌋₊)) atTop (𝓝 (0 * t)) :=
      ha0.mul (tendsto_floor_mul ha ha0 ht)
    rw [zero_mul] at h2
    have hc : Continuous fun x : ℝ => Real.exp (-x) := by fun_prop
    have h3 := (hc.tendsto 0).comp h2
    rw [neg_zero, Real.exp_zero] at h3
    exact h3
  · have := h 1 zero_le_one
    have h3 : Real.exp (-(Δ * 1)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith

end APEX.YM

