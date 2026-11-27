import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp

/-!
# Harmonic polynomials and the spherical Laplacian on `S³` (over `ℝ`)

Everything is proved without `sorry`.

**Part 1 (base change).**  The algebraic theory of `APEX.S3.Harmonic` (proved there over `ℚ`)
is redone here verbatim for an arbitrary field `K` of characteristic `0` (the only change:
the surjectivity lemma `lap_qq_add_surj` takes the shift `c : ℕ` instead of `0 ≤ c : ℚ`).
For `K = ℝ`: `finrank_PP_real : dim_ℝ P_n = C(n+3,3)`, `fischer_real :
P_{n+2} = H_{n+2} ⊕ q·P_n`, `finrank_HH_real : dim_ℝ H_n = (n+1)²`, and the algebraic
identity `sphLap_of_harmonic : (qΔ - E² - 2E) h = -n(n+2) h` for `h ∈ H_n`.

**Part 2 (analytic link).**  On `E4 = Fin 4 → ℝ` with coordinate partial derivatives
`partialF i F x = d/dt F(x[i ↦ t])|_{t=x_i}` and the coordinate Laplacian
`lapF F = Σ_i ∂_i ∂_i F`:
* `hasDerivAt_eval_update`: `∂_i (eval · p) = eval · (pderiv i p)` (and `lapF_eval`:
  `Δ(eval · p) = eval · (lap p)`);
* `hasDerivAt_eval_smul_one`: `d/dt p(t x)|_{t=1} = (E p)(x)`;
  `eval_smul_of_isHomogeneous`: `p(t x) = tⁿ p(x)` for `p ∈ P_n`;
* `lapF_Qrpow_mul`: for `Q(x) = |x|² ≠ 0` and real `s`,
  `Δ(Q^s p) = Q^{s-1}((4s²+4s) p + 4s E p) + Q^s Δp` (the product rule with
  `∇|x|^{2s}·∇p = 2s|x|^{2s-2} E p`, `Δ|x|^{2s} = 2s(2s+2)|x|^{2s-2}` in `ℝ⁴`);
* `sphLapF R f y := Δ(x ↦ f(R x/|x|))(y)`: the Laplacian of the degree-0 homogeneous
  extension of `f|_{S_R}`, restricted to the sphere `|y| = R`;
* `sphLapF_of_mem_PP`: for `p ∈ P_n`, `R > 0`, `|y| = R`:
  `Δ_{S_R} p (y) = Δp(y) - n(n+2)/R² p(y)`;
  `sphLapF_one_eq_sphLap`: on the unit sphere this equals `eval y ((qΔ - E² - 2E) p)`;
* `sphLapF_one_of_harmonic`: **for `h ∈ H_n` and `|y| = 1`,
  `Δ_{S³}(h|_{S³})(y) = -n(n+2) h(y)`**; `sphLapF_of_harmonic`: radius `R` version
  with eigenvalue `-n(n+2)/R²`.

**Part 3 (scaling).**  `sphLapF_scaling : Δ_{S_R} f (y) = R⁻² Δ_{S³}(f ∘ (R·))(y/R)`
(via the dilation chain rule `lapF_comp_smul`), `sphEigen n R = n(n+2)/R²`,
`sphLapF_eq_sphEigen`, `sphEigen_scaling : λ_n(R) = R⁻² λ_n(1)` and
`tendsto_sphEigen : λ_n(R) → 0` as `R → ∞`.

Not proved: completeness of the spherical harmonics in `L²(S³)`; the identification of
`lapF` with Mathlib's `InnerProductSpace.laplacian` on `EuclideanSpace ℝ (Fin 4)`; the
statement that `sphLapF` is intrinsic (it is defined through the extension, as usual).
-/

namespace APEX.S3.Sphere

open MvPolynomial

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [CharZero K]

/-- Polynomials in four variables over a field `K` (characteristic 0 assumed below). -/
abbrev Poly4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- Euclidean Laplacian `Δ p = Σ_i ∂_i ∂_i p`. -/
noncomputable def lap (p : (Poly4 K)) : (Poly4 K) := ∑ i, pderiv i (pderiv i p)

variable (K) in
/-- `q = Σ X_i²`. -/
noncomputable def qq : (Poly4 K) := ∑ i, X i ^ 2

/-- Euler operator `E p = Σ X_i ∂_i p`. -/
noncomputable def euler (p : (Poly4 K)) : (Poly4 K) := ∑ i, X i * pderiv i p

lemma lap_add (f g : (Poly4 K)) : lap (f + g) = lap f + lap g := by
  simp [lap, map_add, Finset.sum_add_distrib]

lemma lap_smul (c : K) (f : (Poly4 K)) : lap (c • f) = c • lap f := by
  simp [lap, Finset.smul_sum]

lemma pderiv_qq (i : Fin 4) : pderiv i (qq K) = 2 * X i := by
  simp only [qq, map_sum, pderiv_pow]
  fin_cases i <;> simp [Fin.sum_univ_four]

lemma pderiv_two (i : Fin 4) : pderiv i (2 : (Poly4 K)) = 0 := by
  rw [← map_ofNat C 2, pderiv_C]

theorem lap_qq : lap (qq K) = 8 := by
  simp only [lap, pderiv_qq, pderiv_mul, pderiv_two, Fin.sum_univ_four]
  simp; norm_num

theorem lap_mul (f g : (Poly4 K)) :
    lap (f * g) = lap f * g + 2 * ∑ i, pderiv i f * pderiv i g + f * lap g := by
  simp only [lap, pderiv_mul, map_add, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem lap_qq_mul (f : (Poly4 K)) : lap ((qq K) * f) = 8 * f + 4 * euler f + (qq K) * lap f := by
  rw [lap_mul, lap_qq, euler]
  simp only [pderiv_qq, Finset.mul_sum]
  have : ∑ i, 2 * (2 * X i * pderiv i f) = ∑ i, 4 * (X i * pderiv i f) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [this]

/-! Euler operator is a derivation-like operator. -/

lemma euler_add (f g : (Poly4 K)) : euler (f + g) = euler f + euler g := by
  simp [euler, map_add, mul_add, Finset.sum_add_distrib]

lemma euler_mul (f g : (Poly4 K)) : euler (f * g) = euler f * g + f * euler g := by
  simp only [euler, pderiv_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma euler_qq : euler (qq K) = 2 * (qq K) := by
  simp only [euler, pderiv_qq]
  simp only [qq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma euler_qq_pow_mul (h : (Poly4 K)) (l : ℕ) (hE : euler h = (l : (Poly4 K)) * h) (j : ℕ) :
    euler (qq K ^ j * h) = ((2 * j + l : ℕ) : (Poly4 K)) * (qq K ^ j * h) := by
  induction j with
  | zero => simpa using hE
  | succ j ih =>
    rw [pow_succ', mul_assoc, euler_mul, ih, euler_qq]
    push_cast; ring

/-- Item 2, in the form `Δ(q^(j+1) h) = 2(j+1)(2l+2j+4) q^j h`, assuming `E h = l h`, `Δ h = 0`. -/
theorem lap_qq_pow_succ_mul (h : (Poly4 K)) (l : ℕ) (hE : euler h = (l : (Poly4 K)) * h)
    (hΔ : lap h = 0) (j : ℕ) :
    lap (qq K ^ (j + 1) * h) = ((2 * (j + 1) * (2 * l + 2 * j + 4) : ℕ) : (Poly4 K)) * (qq K ^ j * h) := by
  induction j with
  | zero => simp [lap_qq_mul, hE, hΔ]; ring
  | succ j ih =>
    rw [pow_succ', mul_assoc, lap_qq_mul, ih, euler_qq_pow_mul h l hE]
    push_cast; ring

/-! ## Euler's identity (local copy of `Mathlib.RingTheory.MvPolynomial.EulerIdentity`,
whose olean is not built in this environment). -/

section EulerCopy
open Finsupp

variable {R σ M : Type*} [CommSemiring R] {φ : MvPolynomial σ R}

lemma isWeightedHomogeneous_pderiv' [AddCancelCommMonoid M] {w : σ → M} {n n' : M} {i : σ}
    (h : φ.IsWeightedHomogeneous w n) (h' : n' + w i = n) :
    (pderiv i φ).IsWeightedHomogeneous w n' := by
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq ↦ ?_) (fun r p _ h ↦ ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, pderiv_monomial, one_mul]
    by_cases hi : m i = 0
    · rw [hi, Nat.cast_zero, monomial_zero]; apply isWeightedHomogeneous_zero
    convert isWeightedHomogeneous_monomial ..
    rw [← add_right_cancel_iff (a := w i), h', ← hm, weight_sub_single_add hi]
  · rw [map_zero]; apply isWeightedHomogeneous_zero
  · rw [map_add]; exact hp.add hq
  · rw [(pderiv i).map_smul]; exact (weightedHomogeneousSubmodule ..).smul_mem _ h

lemma isHomogeneous_pderiv' {n : ℕ} {i : σ} (h : φ.IsHomogeneous n) :
    (pderiv i φ).IsHomogeneous (n - 1) := by
  obtain _ | n := n
  · rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h
    rw [h, pderiv_C]; apply isHomogeneous_zero
  · exact isWeightedHomogeneous_pderiv' h rfl

variable [Fintype σ] {n : ℕ}

lemma sum_weight_X_mul_pderiv' {w : σ → ℕ}
    (h : φ.IsWeightedHomogeneous w n) : ∑ i : σ, w i • (X i * pderiv i φ) = n • φ := by
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at h
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq ↦ ?_) (fun r p _ h ↦ ?_) h
  · rintro _ ⟨m, hm, rfl⟩
    simp_rw [single_eq_monomial, X_mul_pderiv_monomial, smul_smul, ← Finset.sum_smul,
      mul_comm (w _)]
    congr
    rwa [Set.mem_ofPred, weight_apply, sum_fintype] at hm
    intro; apply zero_smul
  · simp
  · simp_rw [map_add, left_distrib, smul_add, Finset.sum_add_distrib, hp, hq]
  · simp_rw [(pderiv _).map_smul, nsmul_eq_mul, mul_smul_comm, ← Finset.smul_sum,
      ← nsmul_eq_mul, h]

/-- Euler's identity for homogeneous polynomials. -/
lemma sum_X_mul_pderiv' (h : φ.IsHomogeneous n) :
    ∑ i : σ, X i * pderiv i φ = n • φ := by
  simp_rw [← sum_weight_X_mul_pderiv' h, Pi.one_apply, one_smul]

end EulerCopy

variable (K) in
/-- The space `P_n` of homogeneous polynomials of degree `n` in 4 variables. -/
abbrev PP (n : ℕ) : Submodule K (Poly4 K) := homogeneousSubmodule (Fin 4) K n

instance (n : ℕ) : FiniteDimensional K (PP K n) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) K n)

/-- Euler's identity: `E f = n f` for `f` homogeneous of degree `n`. -/
theorem euler_of_isHomogeneous {f : (Poly4 K)} {n : ℕ} (hf : f.IsHomogeneous n) :
    euler f = (n : (Poly4 K)) * f := by
  rw [euler, sum_X_mul_pderiv' hf, nsmul_eq_mul]

/-- Item 2: for `h` homogeneous of degree `l` and harmonic,
`Δ(q^(j+1) h) = 2(j+1)(2l+2(j+1)+2) q^j h`. -/
theorem lap_qq_pow_succ_mul_of_harmonic {h : (Poly4 K)} {l : ℕ} (hh : h.IsHomogeneous l)
    (hΔ : lap h = 0) (j : ℕ) :
    lap (qq K ^ (j + 1) * h) =
      ((2 * (j + 1) * (2 * l + 2 * (j + 1) + 2) : ℕ) : (Poly4 K)) * (qq K ^ j * h) := by
  rw [lap_qq_pow_succ_mul h l (euler_of_isHomogeneous hh) hΔ j]
  congr 2

/-- Item 2 in the requested form, for `j ≥ 1`: `Δ(q^j h) = 2j(2l+2j+2) q^(j-1) h`. -/
theorem lap_qq_pow_mul_of_harmonic {h : (Poly4 K)} {l : ℕ} (hh : h.IsHomogeneous l)
    (hΔ : lap h = 0) {j : ℕ} (hj : 1 ≤ j) :
    lap (qq K ^ j * h) = ((2 * j * (2 * l + 2 * j + 2) : ℕ) : (Poly4 K)) * (qq K ^ (j - 1) * h) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [lap_qq_pow_succ_mul_of_harmonic hh hΔ k]
  simp

/-! ## Degree bookkeeping -/

lemma lap_sub (f g : (Poly4 K)) : lap (f - g) = lap f - lap g := by
  simp [lap, map_sub, Finset.sum_sub_distrib]

lemma lap_C_mul (a : K) (f : (Poly4 K)) : lap (C a * f) = C a * lap f := by
  simp [lap, Finset.mul_sum]

lemma qq_isHomogeneous : (qq K).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i 2

lemma qq_mul_mem {f : (Poly4 K)} {k : ℕ} (hf : f ∈ PP K k) : (qq K) * f ∈ PP K (k + 2) := by
  have := qq_isHomogeneous.mul hf
  rw [add_comm] at this; exact this

lemma lap_mem {f : (Poly4 K)} {n : ℕ} (hf : f ∈ PP K n) : lap f ∈ PP K (n - 2) := by
  refine Submodule.sum_mem _ fun i _ => ?_
  have := isHomogeneous_pderiv' (i := i) (isHomogeneous_pderiv' (i := i) hf)
  rwa [Nat.sub_sub] at this

lemma lap_eq_zero_of_lt {f : (Poly4 K)} {n : ℕ} (hf : f ∈ PP K n) (hn : n < 2) : lap f = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : (pderiv i f).IsHomogeneous 0 := by
    have := isHomogeneous_pderiv' (i := i) (show f.IsHomogeneous n from hf)
    rwa [show n - 1 = 0 by omega] at this
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h1
  rw [h1, pderiv_C]

/-- `Δ(q f) = (8 + 4n) f + q Δ f` for `f ∈ P_n`. -/
lemma lap_qq_mul_of_mem {f : (Poly4 K)} {n : ℕ} (hf : f ∈ PP K n) :
    lap ((qq K) * f) = (8 + 4 * (n : (Poly4 K))) * f + (qq K) * lap f := by
  rw [lap_qq_mul, euler_of_isHomogeneous hf]; ring

/-! ## Surjectivity of `Δ ∘ (q ·) + c` on `P_m` (c ∈ ℕ) -/

theorem lap_qq_add_surj (m : ℕ) : ∀ c : ℕ, ∀ f ∈ PP K m,
    ∃ g ∈ PP K m, lap ((qq K) * g) + C (c : K) * g = f := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro c f hf
  obtain ⟨a, ha_def⟩ : ∃ a : K, a = ((8 + 4 * m + c : ℕ) : K) := ⟨_, rfl⟩
  have ha : a ≠ 0 := by rw [ha_def]; exact Nat.cast_ne_zero.mpr (by omega)
  have hCa : C a = 8 + 4 * (m : (Poly4 K)) + C (c : K) := by
    rw [ha_def, map_natCast, map_natCast]; push_cast; ring
  have hinv : (C a * C a⁻¹ : (Poly4 K)) = 1 := by rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  rcases lt_or_ge m 2 with hm | hm
  · have hlf : lap f = 0 := lap_eq_zero_of_lt hf hm
    have hg : C a⁻¹ * f ∈ PP K m := by simpa [smul_eq_C_mul] using Submodule.smul_mem _ a⁻¹ hf
    refine ⟨C a⁻¹ * f, hg, ?_⟩
    have hl := lap_qq_mul_of_mem hg
    rw [lap_C_mul, hlf, mul_zero, mul_zero, add_zero] at hl
    linear_combination hl - C a⁻¹ * f * hCa + f * hinv
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hΔf : lap f ∈ PP K k := by simpa using lap_mem hf
    obtain ⟨g', hg'P, hg'⟩ := IH k (by omega) 0 (lap f) hΔf
    rw [Nat.cast_zero, map_zero, zero_mul, add_zero] at hg'
    have hhP : f - (qq K) * g' ∈ PP K (k + 2) := Submodule.sub_mem _ hf (qq_mul_mem hg'P)
    have hh : lap (f - (qq K) * g') = 0 := by rw [lap_sub, hg', sub_self]
    obtain ⟨g'', hg''P, hg''⟩ := IH k (by omega) (8 + 4 * (k + 2) + c) g' hg'P
    rw [← ha_def] at hg''
    have h1 : C a⁻¹ * (f - (qq K) * g') ∈ PP K (k + 2) := by
      simpa [smul_eq_C_mul] using Submodule.smul_mem _ a⁻¹ hhP
    have hgP : C a⁻¹ * (f - (qq K) * g') + (qq K) * g'' ∈ PP K (k + 2) :=
      Submodule.add_mem _ h1 (qq_mul_mem hg''P)
    refine ⟨_, hgP, ?_⟩
    have hl := lap_qq_mul_of_mem hgP
    have hlg : lap (C a⁻¹ * (f - (qq K) * g') + (qq K) * g'') = lap ((qq K) * g'') := by
      rw [lap_add, lap_C_mul, hh, mul_zero, zero_add]
    rw [hlg] at hl
    linear_combination hl - (C a⁻¹ * (f - (qq K) * g') + (qq K) * g'') * hCa
      + (f - (qq K) * g') * hinv + (qq K) * hg''

/-! ## Linear maps and dimensions -/

variable (K) in
/-- `Δ` as a `K`-linear map. -/
noncomputable def lapL : (Poly4 K) →ₗ[K] (Poly4 K) where
  toFun := lap
  map_add' := lap_add
  map_smul' := lap_smul

variable (K) in
/-- `Δ : P_n → P_{n-2}`. -/
noncomputable def lapOn (n : ℕ) : PP K n →ₗ[K] PP K (n - 2) :=
  (lapL K).restrict fun _ hf => lap_mem hf

variable (K) in
/-- The space `H_n` of harmonic homogeneous polynomials of degree `n`. -/
noncomputable def HH (n : ℕ) : Submodule K (Poly4 K) := PP K n ⊓ LinearMap.ker (lapL K)

lemma mem_HH {f : (Poly4 K)} {n : ℕ} : f ∈ HH K n ↔ f.IsHomogeneous n ∧ lap f = 0 := Iff.rfl

theorem lapOn_surjective (n : ℕ) (hn : 2 ≤ n) : Function.Surjective (lapOn K n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rintro ⟨f, hf⟩
  have hf' : f ∈ PP K k := by simpa using hf
  obtain ⟨g, hgP, hg⟩ := lap_qq_add_surj k 0 f hf'
  rw [Nat.cast_zero, map_zero, zero_mul, add_zero] at hg
  exact ⟨⟨(qq K) * g, qq_mul_mem hgP⟩, Subtype.ext hg⟩

lemma finrank_HH_eq_ker (n : ℕ) :
    Module.finrank K (HH K n) = Module.finrank K (LinearMap.ker (lapOn K n)) := by
  have e := Submodule.equivMapOfInjective (PP K n).subtype Subtype.val_injective
    (LinearMap.ker (lapOn K n))
  have hEq : Submodule.map (PP K n).subtype (LinearMap.ker (lapOn K n)) = HH K n := by
    ext f
    rw [HH, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_map]
    simp only [LinearMap.mem_ker, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa [lapOn, lapL] using congrArg Subtype.val hy⟩
    · rintro ⟨hfP, hf0⟩
      exact ⟨⟨f, hfP⟩, Subtype.ext (by simpa [lapOn, lapL] using hf0), rfl⟩
  rw [e.finrank_eq, (LinearEquiv.ofEq _ _ hEq).finrank_eq]

/-- Item 3a: `dim P_n = C(n+3, 3)`. -/
theorem finrank_PP (n : ℕ) : Module.finrank K (PP K n) = (n + 3).choose 3 := by
  classical
  let S : Set (Fin 4 →₀ ℕ) := {d | d.degree = n}
  let e : S ≃ Sym (Fin 4) n :=
    (Equiv.subtypeEquivRight fun d => by
      simp [S, Finsupp.degree_eq_sum, Finsupp.sum_fintype]).trans (Sym.equivNatSum (Fin 4) n).symm
  rw [(LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 4) K n)).finrank_eq,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) S).finrank_eq,
    (Finsupp.domLCongr (M := K) (R := K) e).finrank_eq, Module.finrank_finsupp_self,
    Sym.card_sym_eq_choose, Fintype.card_fin, show 4 + n - 1 = 3 + n by omega,
    add_comm 3 n, Nat.choose_symm_add]

theorem choose_identity (n : ℕ) : (n + 3).choose 3 = (n + 1).choose 3 + (n + 1) ^ 2 := by
  have t : ∀ n : ℕ, 2 * (n + 1).choose 2 = (n + 1) * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right]
      nlinarith [ih]
  have h2 : (n + 2).choose 2 + (n + 1).choose 2 = (n + 1) ^ 2 := by
    nlinarith [t n, t (n + 1)]
  have a : (n + 3).choose 3 = (n + 2).choose 2 + (n + 2).choose 3 := Nat.choose_succ_succ (n + 2) 2
  have b : (n + 2).choose 3 = (n + 1).choose 2 + (n + 1).choose 3 := Nat.choose_succ_succ (n + 1) 2
  omega

/-- Item 3c: `dim H_n = (n+1)^2`. -/
theorem finrank_HH (n : ℕ) : Module.finrank K (HH K n) = (n + 1) ^ 2 := by
  rcases lt_or_ge n 2 with hn | hn
  · have : HH K n = PP K n := by
      refine le_antisymm inf_le_left fun f hf => ⟨hf, lap_eq_zero_of_lt hf hn⟩
    rw [this, finrank_PP]
    interval_cases n <;> rfl
  · rw [finrank_HH_eq_ker]
    have h := LinearMap.finrank_range_add_finrank_ker (lapOn K n)
    rw [LinearMap.range_eq_top.mpr (lapOn_surjective n hn), finrank_top, finrank_PP,
      finrank_PP] at h
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel] at h
    have := choose_identity (k + 2)
    rw [show k + 2 + 3 = k + 5 from rfl] at h this
    rw [show k + 2 + 1 = k + 3 from rfl] at this ⊢
    omega

/-! ## Fischer decomposition `P_{n+2} = H_{n+2} ⊕ q·P_n` -/

variable (K) in
/-- `T_n = Δ ∘ (q ·) : P_n → P_n`. -/
noncomputable def lapQQ (n : ℕ) : PP K n →ₗ[K] PP K n :=
  ((lapL K) ∘ₗ LinearMap.mulLeft K (qq K)).restrict fun x hx => by
    simpa [lapL] using lap_mem (qq_mul_mem hx)

lemma lapQQ_surjective (n : ℕ) : Function.Surjective (lapQQ K n) := by
  rintro ⟨f, hf⟩
  obtain ⟨g, hgP, hg⟩ := lap_qq_add_surj n 0 f hf
  rw [Nat.cast_zero, map_zero, zero_mul, add_zero] at hg
  exact ⟨⟨g, hgP⟩, Subtype.ext hg⟩

lemma lapQQ_injective (n : ℕ) : Function.Injective (lapQQ K n) :=
  LinearMap.injective_iff_surjective.mpr (lapQQ_surjective n)

/-- If `g ∈ P_n` and `q g` is harmonic, then `g = 0`. -/
lemma eq_zero_of_lap_qq_mul {g : (Poly4 K)} {n : ℕ} (hg : g ∈ PP K n) (h0 : lap ((qq K) * g) = 0) :
    g = 0 := by
  have := @lapQQ_injective K _ _ n ⟨g, hg⟩ 0 (Subtype.ext (by simpa [lapQQ, lapL] using h0))
  simpa using congrArg Subtype.val this

/-- Item 3b (Fischer decomposition): every `f ∈ P_{n+2}` is uniquely `h + q g`
with `h ∈ H_{n+2}` and `g ∈ P_n`. -/
theorem fischer (n : ℕ) {f : (Poly4 K)} (hf : f ∈ PP K (n + 2)) :
    ∃! p : (Poly4 K) × (Poly4 K), p.1 ∈ HH K (n + 2) ∧ p.2 ∈ PP K n ∧ f = p.1 + (qq K) * p.2 := by
  have hΔf : lap f ∈ PP K n := by simpa using lap_mem hf
  obtain ⟨g, hgP, hg⟩ := lap_qq_add_surj n 0 (lap f) hΔf
  rw [Nat.cast_zero, map_zero, zero_mul, add_zero] at hg
  refine ⟨(f - (qq K) * g, g), ⟨⟨Submodule.sub_mem _ hf (qq_mul_mem hgP), ?_⟩, hgP, by ring⟩, ?_⟩
  · show lap (f - (qq K) * g) = 0
    rw [lap_sub, hg, sub_self]
  · rintro ⟨h', g'⟩ ⟨⟨_, hh'⟩, hg'P, hfe⟩
    have hh' : lap h' = 0 := hh'
    have hdiff : lap ((qq K) * (g' - g)) = 0 := by
      have : (qq K) * (g' - g) = f - (qq K) * g - h' := by rw [hfe]; ring
      rw [this, lap_sub, lap_sub, hg, hh']; ring
    have := eq_zero_of_lap_qq_mul (Submodule.sub_mem _ hg'P hgP) hdiff
    have hgg : g' = g := sub_eq_zero.mp this
    subst hgg
    simp only [Prod.mk.injEq, and_true]
    rw [hfe]; ring

/-- `dim H_{n+2} = dim P_{n+2} - dim P_n` (rank–nullity for the surjection `Δ : P_{n+2} → P_n`). -/
theorem finrank_HH_add_finrank_PP (n : ℕ) :
    Module.finrank K (HH K (n + 2)) + Module.finrank K (PP K n) = Module.finrank K (PP K (n + 2)) := by
  rw [finrank_HH_eq_ker]
  have h := LinearMap.finrank_range_add_finrank_ker (lapOn K (n + 2))
  rw [LinearMap.range_eq_top.mpr (lapOn_surjective (n + 2) (by omega)), finrank_top] at h
  exact (add_comm _ _).trans h

/-! ## Item 4: algebraic form of the sphere eigenvalue relation -/

/-- The algebraic "spherical Laplacian" `q Δ - E² - 2E`. -/
noncomputable def sphLap (p : (Poly4 K)) : (Poly4 K) := (qq K) * lap p - euler (euler p) - 2 * euler p

/-- For `h ∈ H_n`: `(qΔ - E² - 2E) h = -n(n+2) h`. -/
theorem sphLap_of_harmonic {h : (Poly4 K)} {n : ℕ} (hh : h ∈ HH K n) :
    sphLap h = -((n * (n + 2) : ℕ) : (Poly4 K)) * h := by
  obtain ⟨hP, hΔ⟩ := hh
  have hΔ' : lap h = 0 := hΔ
  have hE := euler_of_isHomogeneous (show h.IsHomogeneous n from hP)
  have hnP : (n : (Poly4 K)) * h ∈ PP K n := by
    have := Submodule.smul_mem (PP K n) (n : K) hP
    rwa [smul_eq_C_mul, map_natCast] at this
  have hE2 := euler_of_isHomogeneous (show ((n : (Poly4 K)) * h).IsHomogeneous n from hnP)
  rw [sphLap, hΔ', hE, hE2]
  push_cast; ring

/-! ## Part 1 for `K = ℝ` -/

theorem finrank_PP_real (n : ℕ) : Module.finrank ℝ (PP ℝ n) = (n + 3).choose 3 := finrank_PP n

theorem fischer_real (n : ℕ) {f : MvPolynomial (Fin 4) ℝ} (hf : f ∈ PP ℝ (n + 2)) :
    ∃! p : MvPolynomial (Fin 4) ℝ × MvPolynomial (Fin 4) ℝ,
      p.1 ∈ HH ℝ (n + 2) ∧ p.2 ∈ PP ℝ n ∧ f = p.1 + qq ℝ * p.2 := fischer n hf

/-- `dim_ℝ H_n(ℝ) = (n+1)²`. -/
theorem finrank_HH_real (n : ℕ) : Module.finrank ℝ (HH ℝ n) = (n + 1) ^ 2 := finrank_HH n

theorem sphLap_of_harmonic_real {h : MvPolynomial (Fin 4) ℝ} {n : ℕ} (hh : h ∈ HH ℝ n) :
    sphLap h = -((n * (n + 2) : ℕ) : MvPolynomial (Fin 4) ℝ) * h := sphLap_of_harmonic hh

/-! ## Part 2: the analytic link (over `ℝ`) -/

section Analytic

open Filter Topology

/-- Points of `ℝ⁴`, in coordinates. -/
abbrev E4 := Fin 4 → ℝ

/-- Coordinate partial derivative `∂_i F (x) = d/dt F(x₁,…,t,…,x₄)|_{t = x_i}`. -/
noncomputable def partialF (i : Fin 4) (F : E4 → ℝ) (x : E4) : ℝ :=
  deriv (fun t => F (Function.update x i t)) (x i)

/-- The Euclidean Laplacian on `ℝ⁴` in coordinates: `Δ F = Σ_i ∂_i ∂_i F`. -/
noncomputable def lapF (F : E4 → ℝ) (x : E4) : ℝ := ∑ i, partialF i (partialF i F) x

lemma lapF_eq (F : E4 → ℝ) (x : E4) :
    lapF F x = ∑ i, deriv (deriv (fun t => F (Function.update x i t))) (x i) := by
  unfold lapF partialF
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.update_self, Function.update_idem]

/-- The derivative of a polynomial along a coordinate line is the partial derivative. -/
theorem hasDerivAt_eval_update (p : MvPolynomial (Fin 4) ℝ) (x : E4) (i : Fin 4) (t : ℝ) :
    HasDerivAt (fun s => eval (Function.update x i s) p)
      (eval (Function.update x i t) (pderiv i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p j hp =>
    have hX : HasDerivAt (fun s => Function.update x i s j)
        (eval (Function.update x i t) (pderiv i (X j))) t := by
      by_cases h : j = i
      · subst h; simpa using hasDerivAt_id' t
      · simp only [Function.update_of_ne h, pderiv_X_of_ne h, map_zero]
        exact hasDerivAt_const t _
    convert hp.mul hX using 1
    · ext s; simp
    · simp; ring

/-- The radial derivative: `d/dt p(t x) = Σ_i x_i (∂_i p)(t x)`. -/
theorem hasDerivAt_eval_smul (p : MvPolynomial (Fin 4) ℝ) (x : E4) (t : ℝ) :
    HasDerivAt (fun s : ℝ => eval (s • x) p) (∑ i, x i * eval (t • x) (pderiv i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]; exact hp.add hq
  | mul_X p j hp =>
    have hX : HasDerivAt (fun s : ℝ => s * x j) (x j) t := by
      simpa using (hasDerivAt_id t).mul_const (x j)
    convert hp.mul hX using 1
    · ext s; simp
    · have : ∑ i, x i * eval (t • x) (pderiv i (X j : MvPolynomial (Fin 4) ℝ)) = x j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; rw [pderiv_X_of_ne (Ne.symm hb)]; simp
        · simp
      simp only [pderiv_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib, eval_X,
        Pi.smul_apply, smul_eq_mul]
      rw [← this, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

/-- Item 2a (Euler relation): `d/dt p(t x)|_{t=1} = (E p)(x)`. -/
theorem hasDerivAt_eval_smul_one (p : MvPolynomial (Fin 4) ℝ) (x : E4) :
    HasDerivAt (fun s : ℝ => eval (s • x) p) (eval x (euler p)) 1 := by
  convert hasDerivAt_eval_smul p x 1 using 1
  simp [euler]

/-- Item 2b: `p(t x) = t^n p(x)` for `p` homogeneous of degree `n`. -/
theorem eval_smul_of_isHomogeneous {p : MvPolynomial (Fin 4) ℝ} {n : ℕ} (hp : p.IsHomogeneous n)
    (t : ℝ) (x : E4) : eval (t • x) p = t ^ n * eval x p :=
  hp.eval_smul t x

/-- The Laplacian of a polynomial function is the polynomial Laplacian. -/
theorem lapF_eval (p : MvPolynomial (Fin 4) ℝ) (x : E4) :
    lapF (fun y => eval y p) x = eval x (lap p) := by
  rw [lapF_eq, lap, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : deriv (fun t => eval (Function.update x i t) p) =
      fun t => eval (Function.update x i t) (pderiv i p) :=
    funext fun t => (hasDerivAt_eval_update p x i t).deriv
  rw [h1, (hasDerivAt_eval_update (pderiv i p) x i (x i)).deriv, Function.update_eq_self]

/-- `Q(x) = |x|² = Σ x_i²`, as the evaluation of the polynomial `q`. -/
noncomputable def Qf (x : E4) : ℝ := eval x (qq ℝ)

lemma Qf_eq (x : E4) : Qf x = ∑ i, x i ^ 2 := by simp [Qf, qq]

lemma continuous_Qf : Continuous Qf := by
  have : Qf = fun x : E4 => ∑ i, x i ^ 2 := funext Qf_eq
  rw [this]; simp only [Fin.sum_univ_four]
  exact ((((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)).add
    ((continuous_apply 2).pow 2)).add ((continuous_apply 3).pow 2)

lemma hasDerivAt_Qf_update (x : E4) (i : Fin 4) (t : ℝ) :
    HasDerivAt (fun s => Qf (Function.update x i s)) (2 * t) t := by
  have := hasDerivAt_eval_update (qq ℝ) x i t
  rw [pderiv_qq] at this
  simpa [Qf] using this

/-- The second derivative of `Q^s p` along the `i`-th coordinate line through `x` (`Q(x) ≠ 0`). -/
lemma second_deriv_line (p : MvPolynomial (Fin 4) ℝ) (s : ℝ) (x : E4) (i : Fin 4)
    (hx : Qf x ≠ 0) :
    deriv (deriv (fun t => Qf (Function.update x i t) ^ s * eval (Function.update x i t) p))
        (x i) =
      2 * s * Qf x ^ (s - 1) * eval x p
      + 4 * s * (s - 1) * x i ^ 2 * Qf x ^ (s - 1 - 1) * eval x p
      + 4 * s * x i * Qf x ^ (s - 1) * eval x (pderiv i p)
      + Qf x ^ s * eval x (pderiv i (pderiv i p)) := by
  have hG := hasDerivAt_Qf_update x i
  have hP := hasDerivAt_eval_update p x i
  have hP1 := hasDerivAt_eval_update (pderiv i p) x i
  have hGx : Qf (Function.update x i (x i)) = Qf x := by rw [Function.update_eq_self]
  have hev : ∀ᶠ t in 𝓝 (x i), Qf (Function.update x i t) ≠ 0 :=
    (hG (x i)).continuousAt.eventually_ne (by rw [hGx]; exact hx)
  have h1 : deriv (fun t => Qf (Function.update x i t) ^ s * eval (Function.update x i t) p)
      =ᶠ[𝓝 (x i)] fun t => 2 * t * s * Qf (Function.update x i t) ^ (s - 1) *
          eval (Function.update x i t) p
        + Qf (Function.update x i t) ^ s * eval (Function.update x i t) (pderiv i p) := by
    filter_upwards [hev] with t ht
    exact (((hG t).rpow_const (Or.inl ht)).mul (hP t)).deriv
  have hx' : Qf (Function.update x i (x i)) ≠ 0 := by rw [hGx]; exact hx
  have hA : HasDerivAt (fun t : ℝ => 2 * t * s) (2 * 1 * s) (x i) :=
    ((hasDerivAt_id' (x i)).const_mul 2).mul_const s
  have h2 := ((hA.mul ((hG (x i)).rpow_const (p := s - 1) (Or.inl hx'))).mul (hP (x i))).add
    (((hG (x i)).rpow_const (p := s) (Or.inl hx')).mul (hP1 (x i)))
  rw [h1.deriv_eq]
  refine Eq.trans h2.deriv ?_
  simp only [Pi.mul_apply, Function.update_eq_self]
  ring

/-- `Δ(Q^s p) = Q^{s-1}((4s²+4s) p + 4s E p) + Q^s Δp` away from the origin, i.e. the
product rule `Δ(|x|^{2s} p) = |x|^{2s} Δp + 2∇|x|^{2s}·∇p + p Δ|x|^{2s}` in `ℝ⁴` with
`∇|x|^{2s}·∇p = 2s|x|^{2s-2} E p` and `Δ|x|^{2s} = 2s(2s+2)|x|^{2s-2}`. -/
theorem lapF_Qrpow_mul (p : MvPolynomial (Fin 4) ℝ) (s : ℝ) (x : E4) (hx : Qf x ≠ 0) :
    lapF (fun y => Qf y ^ s * eval y p) x =
      Qf x ^ (s - 1) * ((4 * s ^ 2 + 4 * s) * eval x p + 4 * s * eval x (euler p))
        + Qf x ^ s * eval x (lap p) := by
  rw [lapF_eq]
  rw [Finset.sum_congr rfl fun i _ => second_deriv_line p s x i hx]
  have hB : Qf x ^ (s - 1 - 1) * Qf x = Qf x ^ (s - 1) := by
    rw [Real.rpow_sub_one hx (s - 1)]; field_simp
  have hQ := Qf_eq x
  have hE : eval x (euler p) = ∑ i, x i * eval x (pderiv i p) := by simp [euler]
  have hL : eval x (lap p) = ∑ i, eval x (pderiv i (pderiv i p)) := by simp [lap]
  rw [hE, hL]
  simp only [Fin.sum_univ_four] at hQ ⊢
  linear_combination (-(4 * s * (s - 1) * eval x p * Qf x ^ (s - 1 - 1))) * hQ
    + (4 * s * (s - 1) * eval x p) * hB

/-- The same for `p ∈ P_n`: `Δ(Q^s p) = (4s² + 4s + 4sn) Q^{s-1} p + Q^s Δp`. -/
theorem lapF_Qrpow_mul_of_mem {p : MvPolynomial (Fin 4) ℝ} {n : ℕ} (hp : p ∈ PP ℝ n) (s : ℝ)
    (x : E4) (hx : Qf x ≠ 0) :
    lapF (fun y => Qf y ^ s * eval y p) x =
      (4 * s ^ 2 + 4 * s + 4 * s * n) * Qf x ^ (s - 1) * eval x p
        + Qf x ^ s * eval x (lap p) := by
  rw [lapF_Qrpow_mul p s x hx, euler_of_isHomogeneous hp]
  simp only [map_mul, map_natCast]
  ring

/-- `Δ F (x)` only depends on `F` near `x`. -/
lemma lapF_congr {F G : E4 → ℝ} {x : E4} (h : F =ᶠ[𝓝 x] G) : lapF F x = lapF G x := by
  rw [lapF_eq, lapF_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : Continuous fun t : ℝ => Function.update x i t :=
    continuous_const.update i continuous_id
  have ht := hc.continuousAt (x := x i)
  rw [ContinuousAt, Function.update_eq_self] at ht
  have : (fun t => F (Function.update x i t)) =ᶠ[𝓝 (x i)] fun t => G (Function.update x i t) :=
    ht.eventually h
  exact this.deriv.deriv_eq

/-! ### The spherical Laplacian -/

/-- Spherical Laplacian on the sphere `S_R = {|x| = R}` of radius `R`: for a function `f`
(only its values on `S_R` matter), take its degree-0 homogeneous extension
`f̃_R(x) = f(R x / |x|)` to `ℝ⁴ \ {0}` and set `Δ_{S_R} f (y) := (Δ f̃_R)(y)` for `y ∈ S_R`.
For `R = 1` this is `f̃(x) = f(x/|x|)`, `Δ_{S³} f = (Δ f̃)|_{S³}`. -/
noncomputable def sphLapF (R : ℝ) (f : E4 → ℝ) (y : E4) : ℝ :=
  lapF (fun x => f ((R / Real.sqrt (Qf x)) • x)) y

/-- `(R/√Q)^n = Q^{-n/2} R^n` for `Q > 0`. -/
lemma div_sqrt_pow (R Q : ℝ) (hQ : 0 < Q) (n : ℕ) :
    (R / Real.sqrt Q) ^ n = Q ^ (-(n : ℝ) / 2) * R ^ n := by
  rw [div_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (Q ^ _), ← Real.rpow_mul hQ.le,
    neg_div, Real.rpow_neg hQ.le]
  rw [show 1 / (2 : ℝ) * n = n / 2 by ring]
  field_simp

/-- The degree-0 extension of `p ∈ P_n` from `S_R` is `R^n Q^{-n/2} p` near any `y ≠ 0`. -/
lemma ext_eventuallyEq {R : ℝ} {p : MvPolynomial (Fin 4) ℝ} {n : ℕ} (hp : p ∈ PP ℝ n)
    {y : E4} (hy : 0 < Qf y) :
    (fun x => eval ((R / Real.sqrt (Qf x)) • x) p) =ᶠ[𝓝 y]
      fun x => Qf x ^ (-(n : ℝ) / 2) * eval x (C (R ^ n) * p) := by
  have hev : ∀ᶠ x in 𝓝 y, 0 < Qf x := continuous_Qf.continuousAt.eventually (lt_mem_nhds hy)
  filter_upwards [hev] with x hx
  rw [(show p.IsHomogeneous n from hp).eval_smul, div_sqrt_pow R _ hx n]
  simp only [map_mul, eval_C]
  ring

/-- Item 2 (general form): for `p ∈ P_n`, `R > 0` and `|y| = R`,
`Δ_{S_R} (p|_{S_R}) (y) = (Δ p)(y) - n(n+2)/R² · p(y)`. -/
theorem sphLapF_of_mem_PP {R : ℝ} (hR : 0 < R) {p : MvPolynomial (Fin 4) ℝ} {n : ℕ}
    (hp : p ∈ PP ℝ n) {y : E4} (hy : Qf y = R ^ 2) :
    sphLapF R (fun x => eval x p) y = eval y (lap p) - (n * (n + 2) / R ^ 2) * eval y p := by
  have hQ : 0 < Qf y := by rw [hy]; positivity
  have hCp : C (R ^ n) * p ∈ PP ℝ n := by
    have := Submodule.smul_mem (PP ℝ n) (R ^ n) hp
    rwa [smul_eq_C_mul] at this
  rw [sphLapF, lapF_congr (ext_eventuallyEq hp hQ), lapF_Qrpow_mul_of_mem hCp _ y hQ.ne',
    lap_C_mul]
  simp only [map_mul, eval_C]
  -- `(R²)^t = R^(2t)`
  have hpow : ∀ t : ℝ, Qf y ^ t = R ^ (2 * t) := fun t => by
    rw [hy, ← Real.rpow_two, ← Real.rpow_mul hR.le]
  rw [hpow, hpow]
  have hA : R ^ (2 * (-(n : ℝ) / 2)) * R ^ n = 1 := by
    rw [show 2 * (-(n : ℝ) / 2) = -(n : ℝ) by ring, Real.rpow_neg hR.le, Real.rpow_natCast,
      inv_mul_cancel₀ (by positivity)]
  have hB : R ^ (2 * (-(n : ℝ) / 2 - 1)) * R ^ 2 = R ^ (2 * (-(n : ℝ) / 2)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hR]; congr 1; ring
  have hI : R ^ 2 * (R ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  generalize R ^ (2 * (-(n : ℝ) / 2 - 1)) = B at hB ⊢
  generalize R ^ (2 * (-(n : ℝ) / 2)) = A at hA hB ⊢
  rw [div_eq_mul_inv]
  linear_combination (-(n : ℝ) * (n + 2) * eval y p * (R ^ 2)⁻¹ * R ^ n) * hB
    + (-(n : ℝ) * (n + 2) * eval y p * (R ^ 2)⁻¹ + eval y (lap p)) * hA
    + ((n : ℝ) * (n + 2) * eval y p * B * R ^ n) * hI

/-- **Sphere eigenvalue** (radius `R`): for `h ∈ H_n`, `R > 0`, `|y| = R`,
`Δ_{S_R} (h|_{S_R}) (y) = -(n(n+2)/R²) h(y)`. -/
theorem sphLapF_of_harmonic {R : ℝ} (hR : 0 < R) {h : MvPolynomial (Fin 4) ℝ} {n : ℕ}
    (hh : h ∈ HH ℝ n) {y : E4} (hy : Qf y = R ^ 2) :
    sphLapF R (fun x => eval x h) y = -(n * (n + 2) / R ^ 2) * eval y h := by
  rw [sphLapF_of_mem_PP hR hh.1 hy, show lap h = 0 from hh.2, map_zero]
  ring

/-- **Sphere eigenvalue on the unit `S³`**: for `h ∈ H_n` and `|y| = 1`,
`Δ_{S³} (h|_{S³}) (y) = -n(n+2) h(y)`. -/
theorem sphLapF_one_of_harmonic {h : MvPolynomial (Fin 4) ℝ} {n : ℕ} (hh : h ∈ HH ℝ n)
    {y : E4} (hy : Qf y = 1) :
    sphLapF 1 (fun x => eval x h) y = -((n : ℝ) * (n + 2)) * eval y h := by
  rw [sphLapF_of_harmonic one_pos hh (by rw [hy]; norm_num)]
  ring

/-- On the unit sphere the analytic `Δ_{S³}` of `p ∈ P_n` is the evaluation of the
algebraic operator `qΔ - E² - 2E` (`sphLap`). -/
theorem sphLapF_one_eq_sphLap {p : MvPolynomial (Fin 4) ℝ} {n : ℕ} (hp : p ∈ PP ℝ n)
    {y : E4} (hy : Qf y = 1) :
    sphLapF 1 (fun x => eval x p) y = eval y (sphLap p) := by
  have hnP : (n : MvPolynomial (Fin 4) ℝ) * p ∈ PP ℝ n := by
    have := Submodule.smul_mem (PP ℝ n) (n : ℝ) hp
    rwa [smul_eq_C_mul, map_natCast] at this
  rw [sphLapF_of_mem_PP one_pos hp (by rw [hy]; norm_num), sphLap,
    euler_of_isHomogeneous (show p.IsHomogeneous n from hp),
    euler_of_isHomogeneous (show ((n : MvPolynomial (Fin 4) ℝ) * p).IsHomogeneous n from hnP)]
  have hq : eval y (qq ℝ) = 1 := hy
  simp only [map_sub, map_mul, map_natCast, map_ofNat, hq]
  ring

/-! ## Part 3: scaling of the eigenvalues with the radius -/

lemma smul_update (c : ℝ) (x : E4) (i : Fin 4) (t : ℝ) :
    c • Function.update x i t = Function.update (c • x) i (c * t) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- Chain rule for a dilation: `Δ(F(c·))(x) = c² (ΔF)(c x)`. -/
theorem lapF_comp_smul (F : E4 → ℝ) (c : ℝ) (x : E4) :
    lapF (fun z => F (c • z)) x = c ^ 2 * lapF F (c • x) := by
  rw [lapF_eq, lapF_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [smul_update]
  have h1 : deriv (fun t => F (Function.update (c • x) i (c * t))) =
      fun t => c * deriv (fun u => F (Function.update (c • x) i u)) (c * t) :=
    funext fun t => deriv_comp_mul_left (f := fun u => F (Function.update (c • x) i u)) c t
  rw [h1, deriv_const_mul_field,
    deriv_comp_mul_left (f := deriv fun u => F (Function.update (c • x) i u)) c (x i)]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma Qf_smul (c : ℝ) (x : E4) : Qf (c • x) = c ^ 2 * Qf x := by
  simp only [Qf_eq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- The extension `x ↦ f(R x/|x|)` is homogeneous of degree 0 (for every `x`, including `0`). -/
lemma ext_smul (R : ℝ) (f : E4 → ℝ) {c : ℝ} (hc : 0 < c) (z : E4) :
    f ((R / Real.sqrt (Qf (c • z))) • (c • z)) = f ((R / Real.sqrt (Qf z)) • z) := by
  rw [Qf_smul, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le, smul_smul]
  congr 2
  rw [show R / (c * Real.sqrt (Qf z)) * c = (R * c) / (Real.sqrt (Qf z) * c) by ring,
    mul_div_mul_right _ _ hc.ne']

/-- **Definition via scaling is consistent**: for `R > 0`,
`Δ_{S_R} f (y) = R⁻² · Δ_{S³} (f ∘ (R ·)) (y / R)`. -/
theorem sphLapF_scaling {R : ℝ} (hR : 0 < R) (f : E4 → ℝ) (y : E4) :
    sphLapF R f y = (R ^ 2)⁻¹ * sphLapF 1 (fun z => f (R • z)) (R⁻¹ • y) := by
  unfold sphLapF
  have h1 : (fun x => (fun z => f (R • z)) ((1 / Real.sqrt (Qf x)) • x)) =
      fun x => f ((R / Real.sqrt (Qf x)) • x) := by
    funext x; simp only [smul_smul]; congr 2; ring
  have h2 : (fun x => f ((R / Real.sqrt (Qf x)) • x)) =
      fun x => (fun x => f ((R / Real.sqrt (Qf x)) • x)) (R⁻¹ • x) :=
    funext fun x => (ext_smul R f (inv_pos.mpr hR) x).symm
  rw [h1]
  conv_lhs => rw [h2]
  rw [lapF_comp_smul (fun x => f ((R / Real.sqrt (Qf x)) • x)) R⁻¹ y, inv_pow]

/-- `λ_n(R) = n(n+2)/R²`, the `n`-th eigenvalue of `-Δ_{S_R}`. -/
noncomputable def sphEigen (n : ℕ) (R : ℝ) : ℝ := n * (n + 2) / R ^ 2

theorem sphLapF_eq_sphEigen {R : ℝ} (hR : 0 < R) {h : MvPolynomial (Fin 4) ℝ} {n : ℕ}
    (hh : h ∈ HH ℝ n) {y : E4} (hy : Qf y = R ^ 2) :
    sphLapF R (fun x => eval x h) y = -sphEigen n R * eval y h :=
  sphLapF_of_harmonic hR hh hy

/-- Geometric scaling `λ_n(R) = R⁻² λ_n(1)`. -/
theorem sphEigen_scaling (n : ℕ) (R : ℝ) : sphEigen n R = (R ^ 2)⁻¹ * sphEigen n 1 := by
  simp [sphEigen, div_eq_mul_inv]; ring

/-- `λ_n(R) → 0` as `R → ∞`. -/
theorem tendsto_sphEigen (n : ℕ) : Tendsto (sphEigen n) atTop (𝓝 0) := by
  have h : Tendsto (fun R : ℝ => (R ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
  have := h.const_mul ((n : ℝ) * (n + 2))
  rw [mul_zero] at this
  refine this.congr fun R => ?_
  simp [sphEigen, div_eq_mul_inv]

end Analytic

end APEX.S3.Sphere


