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

/-!
# Harmonic polynomials on `ℝ⁴` / `ℚ⁴` (algebraic part of the S³ library)

We work in `Poly4 = MvPolynomial (Fin 4) ℚ` with the Laplacian `lap p = Σ_i ∂_i ∂_i p`,
`qq = Σ X_i²` and the Euler operator `euler p = Σ X_i ∂_i p`.  Fully proved (no sorry):

1. `lap_qq : Δ q = 8`; `lap_mul : Δ(fg) = Δf·g + 2 Σ ∂_i f ∂_i g + f Δg`;
   `lap_qq_mul : Δ(q f) = 8 f + 4 E f + q Δf`.
2. `euler_of_isHomogeneous` (Euler's identity `E f = n f`, a local copy of Mathlib's
   `IsHomogeneous.sum_X_mul_pderiv`, whose module is not built here) and
   `lap_qq_pow_mul_of_harmonic : h homogeneous of degree l, Δh = 0, j ≥ 1 ⟹
   Δ(q^j h) = 2j(2l+2j+2) q^(j-1) h`.
3. `finrank_PP : dim P_n = C(n+3,3)`; `lap_qq_add_surj` (for `c ≥ 0`, `g ↦ Δ(qg) + c g` is
   onto `P_m`); `lapOn_surjective : Δ : P_n → P_{n-2}` is onto for `n ≥ 2`;
   `fischer : P_{n+2} = H_{n+2} ⊕ q·P_n` (unique decomposition);
   `finrank_HH_add_finrank_PP`, `choose_identity : C(n+3,3) = C(n+1,3) + (n+1)²` and
   `finrank_HH : dim H_n = (n+1)²` for all `n`.
4. `sphLap_of_harmonic : (qΔ - E² - 2E) h = -n(n+2) h` for `h ∈ H_n`. This is only the
   *algebraic* identity.  The analytic statement `Δ_{S³} (h|_{S³}) = -n(n+2) h|_{S³}` still
   requires the polar decomposition `Δ = ∂_r² + (3/r)∂_r + r⁻² Δ_{S³}` (equivalently the
   identification `r²Δ = r²∂_r² + 3 r∂_r + Δ_{S³}` with `E = r∂_r`), which is NOT proved here.
-/

namespace APEX.S3

open MvPolynomial

/-- Polynomials in four variables over `ℚ`. -/
abbrev Poly4 := MvPolynomial (Fin 4) ℚ

/-- Euclidean Laplacian `Δ p = Σ_i ∂_i ∂_i p`. -/
noncomputable def lap (p : Poly4) : Poly4 := ∑ i, pderiv i (pderiv i p)

/-- `q = Σ X_i²`. -/
noncomputable def qq : Poly4 := ∑ i, X i ^ 2

/-- Euler operator `E p = Σ X_i ∂_i p`. -/
noncomputable def euler (p : Poly4) : Poly4 := ∑ i, X i * pderiv i p

lemma lap_add (f g : Poly4) : lap (f + g) = lap f + lap g := by
  simp [lap, map_add, Finset.sum_add_distrib]

lemma lap_smul (c : ℚ) (f : Poly4) : lap (c • f) = c • lap f := by
  simp [lap, Finset.smul_sum]

lemma pderiv_qq (i : Fin 4) : pderiv i qq = 2 * X i := by
  simp only [qq, map_sum, pderiv_pow]
  fin_cases i <;> simp [Fin.sum_univ_four]

lemma pderiv_two (i : Fin 4) : pderiv i (2 : Poly4) = 0 := by
  rw [← map_ofNat C 2, pderiv_C]

theorem lap_qq : lap qq = 8 := by
  simp only [lap, pderiv_qq, pderiv_mul, pderiv_two, Fin.sum_univ_four]
  simp; norm_num

theorem lap_mul (f g : Poly4) :
    lap (f * g) = lap f * g + 2 * ∑ i, pderiv i f * pderiv i g + f * lap g := by
  simp only [lap, pderiv_mul, map_add, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem lap_qq_mul (f : Poly4) : lap (qq * f) = 8 * f + 4 * euler f + qq * lap f := by
  rw [lap_mul, lap_qq, euler]
  simp only [pderiv_qq, Finset.mul_sum]
  have : ∑ i, 2 * (2 * X i * pderiv i f) = ∑ i, 4 * (X i * pderiv i f) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [this]

/-! Euler operator is a derivation-like operator. -/

lemma euler_add (f g : Poly4) : euler (f + g) = euler f + euler g := by
  simp [euler, map_add, mul_add, Finset.sum_add_distrib]

lemma euler_mul (f g : Poly4) : euler (f * g) = euler f * g + f * euler g := by
  simp only [euler, pderiv_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma euler_qq : euler qq = 2 * qq := by
  simp only [euler, pderiv_qq]
  simp only [qq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma euler_qq_pow_mul (h : Poly4) (l : ℕ) (hE : euler h = (l : Poly4) * h) (j : ℕ) :
    euler (qq ^ j * h) = ((2 * j + l : ℕ) : Poly4) * (qq ^ j * h) := by
  induction j with
  | zero => simpa using hE
  | succ j ih =>
    rw [pow_succ', mul_assoc, euler_mul, ih, euler_qq]
    push_cast; ring

/-- Item 2, in the form `Δ(q^(j+1) h) = 2(j+1)(2l+2j+4) q^j h`, assuming `E h = l h`, `Δ h = 0`. -/
theorem lap_qq_pow_succ_mul (h : Poly4) (l : ℕ) (hE : euler h = (l : Poly4) * h)
    (hΔ : lap h = 0) (j : ℕ) :
    lap (qq ^ (j + 1) * h) = ((2 * (j + 1) * (2 * l + 2 * j + 4) : ℕ) : Poly4) * (qq ^ j * h) := by
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

/-- The space `P_n` of homogeneous polynomials of degree `n` in 4 variables. -/
abbrev PP (n : ℕ) : Submodule ℚ Poly4 := homogeneousSubmodule (Fin 4) ℚ n

instance (n : ℕ) : FiniteDimensional ℚ (PP n) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) ℚ n)

/-- Euler's identity: `E f = n f` for `f` homogeneous of degree `n`. -/
theorem euler_of_isHomogeneous {f : Poly4} {n : ℕ} (hf : f.IsHomogeneous n) :
    euler f = (n : Poly4) * f := by
  rw [euler, sum_X_mul_pderiv' hf, nsmul_eq_mul]

/-- Item 2: for `h` homogeneous of degree `l` and harmonic,
`Δ(q^(j+1) h) = 2(j+1)(2l+2(j+1)+2) q^j h`. -/
theorem lap_qq_pow_succ_mul_of_harmonic {h : Poly4} {l : ℕ} (hh : h.IsHomogeneous l)
    (hΔ : lap h = 0) (j : ℕ) :
    lap (qq ^ (j + 1) * h) =
      ((2 * (j + 1) * (2 * l + 2 * (j + 1) + 2) : ℕ) : Poly4) * (qq ^ j * h) := by
  rw [lap_qq_pow_succ_mul h l (euler_of_isHomogeneous hh) hΔ j]
  congr 2

/-- Item 2 in the requested form, for `j ≥ 1`: `Δ(q^j h) = 2j(2l+2j+2) q^(j-1) h`. -/
theorem lap_qq_pow_mul_of_harmonic {h : Poly4} {l : ℕ} (hh : h.IsHomogeneous l)
    (hΔ : lap h = 0) {j : ℕ} (hj : 1 ≤ j) :
    lap (qq ^ j * h) = ((2 * j * (2 * l + 2 * j + 2) : ℕ) : Poly4) * (qq ^ (j - 1) * h) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [lap_qq_pow_succ_mul_of_harmonic hh hΔ k]
  simp

/-! ## Degree bookkeeping -/

lemma lap_sub (f g : Poly4) : lap (f - g) = lap f - lap g := by
  simp [lap, map_sub, Finset.sum_sub_distrib]

lemma lap_C_mul (a : ℚ) (f : Poly4) : lap (C a * f) = C a * lap f := by
  simp [lap, Finset.mul_sum]

lemma qq_isHomogeneous : qq.IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i 2

lemma qq_mul_mem {f : Poly4} {k : ℕ} (hf : f ∈ PP k) : qq * f ∈ PP (k + 2) := by
  have := qq_isHomogeneous.mul hf
  rw [add_comm] at this; exact this

lemma lap_mem {f : Poly4} {n : ℕ} (hf : f ∈ PP n) : lap f ∈ PP (n - 2) := by
  refine Submodule.sum_mem _ fun i _ => ?_
  have := isHomogeneous_pderiv' (i := i) (isHomogeneous_pderiv' (i := i) hf)
  rwa [Nat.sub_sub] at this

lemma lap_eq_zero_of_lt {f : Poly4} {n : ℕ} (hf : f ∈ PP n) (hn : n < 2) : lap f = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : (pderiv i f).IsHomogeneous 0 := by
    have := isHomogeneous_pderiv' (i := i) (show f.IsHomogeneous n from hf)
    rwa [show n - 1 = 0 by omega] at this
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h1
  rw [h1, pderiv_C]

/-- `Δ(q f) = (8 + 4n) f + q Δ f` for `f ∈ P_n`. -/
lemma lap_qq_mul_of_mem {f : Poly4} {n : ℕ} (hf : f ∈ PP n) :
    lap (qq * f) = (8 + 4 * (n : Poly4)) * f + qq * lap f := by
  rw [lap_qq_mul, euler_of_isHomogeneous hf]; ring

/-! ## Surjectivity of `Δ ∘ (q ·) + c` on `P_m` (c ≥ 0) -/

theorem lap_qq_add_surj (m : ℕ) : ∀ c : ℚ, 0 ≤ c → ∀ f ∈ PP m,
    ∃ g ∈ PP m, lap (qq * g) + C c * g = f := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro c hc f hf
  set a : ℚ := 8 + 4 * m + c with ha_def
  have ha : a ≠ 0 := by positivity
  have hCa : C a = 8 + 4 * (m : Poly4) + C c := by
    rw [ha_def, map_add, map_add, map_mul, map_natCast, map_ofNat C 8, map_ofNat C 4]
  have hinv : (C a * C a⁻¹ : Poly4) = 1 := by rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  rcases lt_or_ge m 2 with hm | hm
  · have hlf : lap f = 0 := lap_eq_zero_of_lt hf hm
    have hg : C a⁻¹ * f ∈ PP m := by simpa [smul_eq_C_mul] using Submodule.smul_mem _ a⁻¹ hf
    refine ⟨C a⁻¹ * f, hg, ?_⟩
    have hl := lap_qq_mul_of_mem hg
    rw [lap_C_mul, hlf, mul_zero, mul_zero, add_zero] at hl
    linear_combination hl - C a⁻¹ * f * hCa + f * hinv
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hΔf : lap f ∈ PP k := by simpa using lap_mem hf
    obtain ⟨g', hg'P, hg'⟩ := IH k (by omega) 0 le_rfl (lap f) hΔf
    rw [map_zero, zero_mul, add_zero] at hg'
    have hhP : f - qq * g' ∈ PP (k + 2) := Submodule.sub_mem _ hf (qq_mul_mem hg'P)
    have hh : lap (f - qq * g') = 0 := by rw [lap_sub, hg', sub_self]
    obtain ⟨g'', hg''P, hg''⟩ := IH k (by omega) a (by positivity) g' hg'P
    have h1 : C a⁻¹ * (f - qq * g') ∈ PP (k + 2) := by
      simpa [smul_eq_C_mul] using Submodule.smul_mem _ a⁻¹ hhP
    have hgP : C a⁻¹ * (f - qq * g') + qq * g'' ∈ PP (k + 2) :=
      Submodule.add_mem _ h1 (qq_mul_mem hg''P)
    refine ⟨_, hgP, ?_⟩
    have hl := lap_qq_mul_of_mem hgP
    have hlg : lap (C a⁻¹ * (f - qq * g') + qq * g'') = lap (qq * g'') := by
      rw [lap_add, lap_C_mul, hh, mul_zero, zero_add]
    rw [hlg] at hl
    linear_combination hl - (C a⁻¹ * (f - qq * g') + qq * g'') * hCa
      + (f - qq * g') * hinv + qq * hg''

/-! ## Linear maps and dimensions -/

/-- `Δ` as a `ℚ`-linear map. -/
noncomputable def lapL : Poly4 →ₗ[ℚ] Poly4 where
  toFun := lap
  map_add' := lap_add
  map_smul' := lap_smul

/-- `Δ : P_n → P_{n-2}`. -/
noncomputable def lapOn (n : ℕ) : PP n →ₗ[ℚ] PP (n - 2) :=
  lapL.restrict fun _ hf => lap_mem hf

/-- The space `H_n` of harmonic homogeneous polynomials of degree `n`. -/
noncomputable def HH (n : ℕ) : Submodule ℚ Poly4 := PP n ⊓ LinearMap.ker lapL

lemma mem_HH {f : Poly4} {n : ℕ} : f ∈ HH n ↔ f.IsHomogeneous n ∧ lap f = 0 := Iff.rfl

theorem lapOn_surjective (n : ℕ) (hn : 2 ≤ n) : Function.Surjective (lapOn n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rintro ⟨f, hf⟩
  have hf' : f ∈ PP k := by simpa using hf
  obtain ⟨g, hgP, hg⟩ := lap_qq_add_surj k 0 le_rfl f hf'
  rw [map_zero, zero_mul, add_zero] at hg
  exact ⟨⟨qq * g, qq_mul_mem hgP⟩, Subtype.ext hg⟩

lemma finrank_HH_eq_ker (n : ℕ) :
    Module.finrank ℚ (HH n) = Module.finrank ℚ (LinearMap.ker (lapOn n)) := by
  have e := Submodule.equivMapOfInjective (PP n).subtype Subtype.val_injective
    (LinearMap.ker (lapOn n))
  have hEq : Submodule.map (PP n).subtype (LinearMap.ker (lapOn n)) = HH n := by
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
theorem finrank_PP (n : ℕ) : Module.finrank ℚ (PP n) = (n + 3).choose 3 := by
  classical
  let S : Set (Fin 4 →₀ ℕ) := {d | d.degree = n}
  let e : S ≃ Sym (Fin 4) n :=
    (Equiv.subtypeEquivRight fun d => by
      simp [S, Finsupp.degree_eq_sum, Finsupp.sum_fintype]).trans (Sym.equivNatSum (Fin 4) n).symm
  rw [(LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 4) ℚ n)).finrank_eq,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := ℚ) S).finrank_eq,
    (Finsupp.domLCongr (M := ℚ) (R := ℚ) e).finrank_eq, Module.finrank_finsupp_self,
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
theorem finrank_HH (n : ℕ) : Module.finrank ℚ (HH n) = (n + 1) ^ 2 := by
  rcases lt_or_ge n 2 with hn | hn
  · have : HH n = PP n := by
      refine le_antisymm inf_le_left fun f hf => ⟨hf, lap_eq_zero_of_lt hf hn⟩
    rw [this, finrank_PP]
    interval_cases n <;> rfl
  · rw [finrank_HH_eq_ker]
    have h := LinearMap.finrank_range_add_finrank_ker (lapOn n)
    rw [LinearMap.range_eq_top.mpr (lapOn_surjective n hn), finrank_top, finrank_PP,
      finrank_PP] at h
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel] at h
    have := choose_identity (k + 2)
    rw [show k + 2 + 3 = k + 5 from rfl] at h this
    rw [show k + 2 + 1 = k + 3 from rfl] at this ⊢
    omega

/-! ## Fischer decomposition `P_{n+2} = H_{n+2} ⊕ q·P_n` -/

/-- `T_n = Δ ∘ (q ·) : P_n → P_n`. -/
noncomputable def lapQQ (n : ℕ) : PP n →ₗ[ℚ] PP n :=
  (lapL ∘ₗ LinearMap.mulLeft ℚ qq).restrict fun x hx => by
    simpa [lapL] using lap_mem (qq_mul_mem hx)

lemma lapQQ_surjective (n : ℕ) : Function.Surjective (lapQQ n) := by
  rintro ⟨f, hf⟩
  obtain ⟨g, hgP, hg⟩ := lap_qq_add_surj n 0 le_rfl f hf
  rw [map_zero, zero_mul, add_zero] at hg
  exact ⟨⟨g, hgP⟩, Subtype.ext hg⟩

lemma lapQQ_injective (n : ℕ) : Function.Injective (lapQQ n) :=
  LinearMap.injective_iff_surjective.mpr (lapQQ_surjective n)

/-- If `g ∈ P_n` and `q g` is harmonic, then `g = 0`. -/
lemma eq_zero_of_lap_qq_mul {g : Poly4} {n : ℕ} (hg : g ∈ PP n) (h0 : lap (qq * g) = 0) :
    g = 0 := by
  have := @lapQQ_injective n ⟨g, hg⟩ 0 (Subtype.ext (by simpa [lapQQ, lapL] using h0))
  simpa using congrArg Subtype.val this

/-- Item 3b (Fischer decomposition): every `f ∈ P_{n+2}` is uniquely `h + q g`
with `h ∈ H_{n+2}` and `g ∈ P_n`. -/
theorem fischer (n : ℕ) {f : Poly4} (hf : f ∈ PP (n + 2)) :
    ∃! p : Poly4 × Poly4, p.1 ∈ HH (n + 2) ∧ p.2 ∈ PP n ∧ f = p.1 + qq * p.2 := by
  have hΔf : lap f ∈ PP n := by simpa using lap_mem hf
  obtain ⟨g, hgP, hg⟩ := lap_qq_add_surj n 0 le_rfl (lap f) hΔf
  rw [map_zero, zero_mul, add_zero] at hg
  refine ⟨(f - qq * g, g), ⟨⟨Submodule.sub_mem _ hf (qq_mul_mem hgP), ?_⟩, hgP, by ring⟩, ?_⟩
  · show lap (f - qq * g) = 0
    rw [lap_sub, hg, sub_self]
  · rintro ⟨h', g'⟩ ⟨⟨_, hh'⟩, hg'P, hfe⟩
    have hh' : lap h' = 0 := hh'
    have hdiff : lap (qq * (g' - g)) = 0 := by
      have : qq * (g' - g) = f - qq * g - h' := by rw [hfe]; ring
      rw [this, lap_sub, lap_sub, hg, hh']; ring
    have := eq_zero_of_lap_qq_mul (Submodule.sub_mem _ hg'P hgP) hdiff
    have hgg : g' = g := sub_eq_zero.mp this
    subst hgg
    simp only [Prod.mk.injEq, and_true]
    rw [hfe]; ring

/-- `dim H_{n+2} = dim P_{n+2} - dim P_n` (rank–nullity for the surjection `Δ : P_{n+2} → P_n`). -/
theorem finrank_HH_add_finrank_PP (n : ℕ) :
    Module.finrank ℚ (HH (n + 2)) + Module.finrank ℚ (PP n) = Module.finrank ℚ (PP (n + 2)) := by
  rw [finrank_HH_eq_ker]
  have h := LinearMap.finrank_range_add_finrank_ker (lapOn (n + 2))
  rw [LinearMap.range_eq_top.mpr (lapOn_surjective (n + 2) (by omega)), finrank_top] at h
  exact (add_comm _ _).trans h

/-! ## Item 4: algebraic form of the sphere eigenvalue relation -/

/-- The algebraic "spherical Laplacian" `q Δ - E² - 2E`. -/
noncomputable def sphLap (p : Poly4) : Poly4 := qq * lap p - euler (euler p) - 2 * euler p

/-- For `h ∈ H_n`: `(qΔ - E² - 2E) h = -n(n+2) h`. -/
theorem sphLap_of_harmonic {h : Poly4} {n : ℕ} (hh : h ∈ HH n) :
    sphLap h = -((n * (n + 2) : ℕ) : Poly4) * h := by
  obtain ⟨hP, hΔ⟩ := hh
  have hΔ' : lap h = 0 := hΔ
  have hE := euler_of_isHomogeneous (show h.IsHomogeneous n from hP)
  have hnP : (n : Poly4) * h ∈ PP n := by
    have := Submodule.smul_mem (PP n) (n : ℚ) hP
    rwa [smul_eq_C_mul, map_natCast] at this
  have hE2 := euler_of_isHomogeneous (show ((n : Poly4) * h).IsHomogeneous n from hnP)
  rw [sphLap, hΔ', hE, hE2]
  push_cast; ring

end APEX.S3

