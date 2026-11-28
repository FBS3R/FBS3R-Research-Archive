import APEX.Blockade.Asymptotics
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Range-`r` blockade: spectral measures, moments and the Gaussian limit (method-of-moments data)

`AR r n` is the real symmetric adjacency matrix `A_{n,r}`, `eig r n` its eigenvalues
(`Matrix.IsHermitian.eigenvalues`), and
`mu r n = (1/a_{n,r}) ∑_λ δ_{λ/√n}` the empirical spectral measure (a probability measure).
`phi s` is the `N(0,s)` density `e^{−x²/(2s)}/√(2πs)`; `σ_r² = sigmaSq r`.

* `AR_hermitian`, `trace_pow_eq_sum` : `Tr A^k = ∑ λ_i^k` (spectral theorem).
* `moment_mu` (a) : `∫ x^k dμ_n = Tr(A_{n,r}^k) / (a_{n,r} √n^k)`.
* `gauss_moment_even`, `gauss_moment_odd` : `∫ x^{2m} φ_s = (2m−1)!! s^m`, odd moments `0`
  (integration by parts from `integral_gaussian`).
* `moment_tendsto` (b) : for `r ≥ 1` and all `k`, `∫ x^k dμ_n → ∫ x^k φ_{σ_r²}(x) dx`.
* `poly_tendsto` (d) : `∫ f dμ_n → ∫ f φ_{σ_r²}` for every `f : ℝ[X]`.
* `tight` (c) : `∀ ε > 0, ∃ R > 0, ∀ n, μ_n {x : R < |x|} ≤ ε`.

Weak convergence `μ_n ⇒ N(0, σ_r²)` (bounded continuous test functions) is proved in
`APEX/Blockade/WeakLimit.lean` (`weak_limit`), with the limit given by the explicit density `phi`
(Mathlib's `ProbabilityTheory.gaussianReal` is not compiled in the build used).
-/

namespace APEX.Blockade.Gaussian

open Finset Filter Topology MeasureTheory
open APEX.Blockade.Asymptotics

/-! ### 1. Symmetry and the spectral moment identity -/

lemma flip_flip {w : List Bool} {i : ℕ} (h : i < w.length) : flip (flip w i) i = w := by
  unfold flip
  simp [List.getD_eq_getElem?_getD, h]

lemma adj_symm {r n : ℕ} (u v : V r n) : Adj u.1 v.1 → Adj v.1 u.1 := by
  rintro ⟨i, hi, hv⟩
  refine ⟨i, ?_, ?_⟩
  · rw [hv, length_flip]; exact hi
  · rw [hv, flip_flip (mem_range.1 hi)]

/-- The adjacency matrix over `ℝ`. -/
noncomputable def AR (r n : ℕ) : Matrix (V r n) (V r n) ℝ := (adjMat r n).map (Int.cast)

lemma AR_hermitian (r n : ℕ) : (AR r n).IsHermitian := by
  ext u v
  simp only [AR, Matrix.conjTranspose_apply, Matrix.map_apply, adjMat, Matrix.of_apply, star_trivial]
  by_cases h : Adj u.1 v.1
  · rw [if_pos h, if_pos (adj_symm u v h)]
  · rw [if_neg h, if_neg (fun h' => h (adj_symm v u h'))]

/-- Eigenvalues of `A_{n,r}`. -/
noncomputable def eig (r n : ℕ) : V r n → ℝ := (AR_hermitian r n).eigenvalues

theorem trace_pow_eq_sum (r n k : ℕ) : (Mk k r n : ℝ) = ∑ i, eig r n i ^ k := by
  classical
  have hA := AR_hermitian r n
  have e1 : (Mk k r n : ℝ) = Matrix.trace (AR r n ^ k) := by
    rw [show AR r n ^ k = (Int.castRingHom ℝ).mapMatrix (adjMat r n ^ k) by rw [map_pow]; rfl, Mk]
    simp [Matrix.trace]
  rw [e1]
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

lemma adm_replicate (r : ℕ) : ∀ n, Adm r (List.replicate n false)
  | 0 => trivial
  | n + 1 => by simpa [List.replicate_succ, Adm] using adm_replicate r n

lemma card_V (r n : ℕ) : Fintype.card (V r n) = a r n := by
  simp [V, a]

lemma a_pos (r n : ℕ) : 0 < a r n := by
  unfold a
  exact Finset.card_pos.2 ⟨List.replicate n false, mem_C.2 ⟨by simp, adm_replicate r n⟩⟩

/-! ### 2. The empirical spectral measure -/

/-- `μ_n = (1/a_n) ∑_λ δ_{λ/√n}`. -/
noncomputable def mu (r n : ℕ) : Measure ℝ :=
  ((a r n : ENNReal)⁻¹) • ∑ i : V r n, Measure.dirac (eig r n i / Real.sqrt n)

lemma integral_sum_dirac {ι : Type*} (s : Finset ι) (x : ι → ℝ) (g : ℝ → ℝ) :
    Integrable g (∑ i ∈ s, Measure.dirac (x i)) ∧
      ∫ y, g y ∂(∑ i ∈ s, Measure.dirac (x i)) = ∑ i ∈ s, g (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hd : Integrable g (Measure.dirac (x j)) := integrable_dirac (by simp)
    rw [sum_insert hj, sum_insert hj]
    refine ⟨hd.add_measure ih.1, ?_⟩
    rw [integral_add_measure hd ih.1, integral_dirac, ih.2]

theorem integral_mu (r n : ℕ) (g : ℝ → ℝ) :
    ∫ y, g y ∂(mu r n) = (a r n : ℝ)⁻¹ * ∑ i, g (eig r n i / Real.sqrt n) := by
  rw [mu, integral_smul_measure, (integral_sum_dirac univ _ g).2, smul_eq_mul]
  simp

theorem mu_univ (r n : ℕ) : mu r n Set.univ = 1 := by
  have h0 : (a r n : ENNReal) ≠ 0 := by exact_mod_cast (a_pos r n).ne'
  simp only [mu, smul_apply, Measure.finsetSum_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), sum_const, card_univ, card_V, smul_eq_mul, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _)

instance (r n : ℕ) : IsProbabilityMeasure (mu r n) := ⟨mu_univ r n⟩

/-- **(a) Moment identity**: `∫ x^k dμ_n = Tr(A_{n,r}^k) / (a_{n,r} · √n^k)`. -/
theorem moment_mu (r n k : ℕ) :
    ∫ y, y ^ k ∂(mu r n) = (Mk k r n : ℝ) / ((a r n : ℝ) * Real.sqrt n ^ k) := by
  rw [integral_mu, trace_pow_eq_sum]
  simp only [div_pow]
  rw [← sum_div]
  field_simp

/-! ### 3. Gaussian moments -/

/-- `gI b k = ∫ x^k e^{−b x²} dx`. -/
noncomputable def gI (b : ℝ) (k : ℕ) : ℝ := ∫ x : ℝ, x ^ k * Real.exp (-b * x ^ 2)

lemma integrable_pow_gauss {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ)) (by have := k.cast_nonneg (α := ℝ); linarith)
  simpa [Real.rpow_natCast] using this

lemma hasDerivAt_gauss (b : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ (k + 1) * Real.exp (-b * x ^ 2))
      ((k + 1 : ℝ) * (x ^ k * Real.exp (-b * x ^ 2)) - 2 * b * (x ^ (k + 2) * Real.exp (-b * x ^ 2))) x := by
  have h1 := hasDerivAt_pow (k + 1) x
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-b * x ^ 2)) (Real.exp (-b * x ^ 2) * (-b * (2 * x))) x := by
    have := ((hasDerivAt_pow 2 x).const_mul (-b)).exp
    simpa using this
  convert h1.mul h2 using 1
  push_cast
  ring

lemma gI_succ_succ {b : ℝ} (hb : 0 < b) (k : ℕ) : gI b (k + 2) = (k + 1) / (2 * b) * gI b k := by
  have h := integral_eq_zero_of_hasDerivAt_of_integrable (hasDerivAt_gauss b k)
    (((integrable_pow_gauss hb k).const_mul _).sub ((integrable_pow_gauss hb (k + 2)).const_mul _))
    (integrable_pow_gauss hb (k + 1))
  rw [integral_sub ((integrable_pow_gauss hb k).const_mul _)
    ((integrable_pow_gauss hb (k + 2)).const_mul _), integral_const_mul, integral_const_mul] at h
  unfold gI
  have hb2 : (2 * b) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hb2]
  linarith

lemma gI_zero (b : ℝ) : gI b 0 = Real.sqrt (Real.pi / b) := by
  rw [gI]; simp only [pow_zero, one_mul]; exact integral_gaussian b

lemma gI_odd {b : ℝ} (k : ℕ) (hk : Odd k) : gI b k = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) volume
  simp only [hk.neg_pow, neg_sq, neg_mul, integral_neg] at h
  unfold gI
  simp only [neg_mul] 
  linarith

lemma gI_even {b : ℝ} (hb : 0 < b) : ∀ m : ℕ,
    gI b (2 * m) = (Nat.doubleFactorial (2 * m - 1) : ℝ) / (2 * b) ^ m * Real.sqrt (Real.pi / b)
  | 0 => by simp [gI_zero]
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, gI_succ_succ hb, gI_even hb m,
      show 2 * m + 2 - 1 = 2 * m + 1 by omega, Nat.doubleFactorial_add_one]
    have hb2 : (2 * b) ≠ 0 := by positivity
    rw [show 2 * m - 1 = 2 * m - 1 by rfl]
    push_cast
    field_simp
    ring

/-- The density of `N(0, s)`. -/
noncomputable def phi (s x : ℝ) : ℝ := Real.exp (-x ^ 2 / (2 * s)) / Real.sqrt (2 * Real.pi * s)

lemma integral_pow_phi (s : ℝ) (k : ℕ) :
    ∫ x, x ^ k * phi s x = gI (1 / (2 * s)) k / Real.sqrt (2 * Real.pi * s) := by
  unfold gI phi
  rw [← integral_div]
  congr 1; funext x
  rw [mul_div_assoc]
  congr 3
  ring

/-- **Gaussian moments**: `∫ x^{2m} φ_s = (2m−1)!! s^m`. -/
theorem gauss_moment_even {s : ℝ} (hs : 0 < s) (m : ℕ) :
    ∫ x, x ^ (2 * m) * phi s x = (Nat.doubleFactorial (2 * m - 1) : ℝ) * s ^ m := by
  rw [integral_pow_phi, gI_even (by positivity)]
  have e : Real.pi / (1 / (2 * s)) = 2 * Real.pi * s := by field_simp
  rw [e]
  have hq : 0 < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.2 (by positivity)
  field_simp
  rw [← mul_pow, one_div, inv_mul_cancel₀ hs.ne', one_pow]

theorem gauss_moment_odd (s : ℝ) {k : ℕ} (hk : Odd k) : ∫ x, x ^ k * phi s x = 0 := by
  rw [integral_pow_phi, gI_odd k hk, zero_div]

lemma integrable_pow_phi {s : ℝ} (hs : 0 < s) (k : ℕ) : Integrable (fun x => x ^ k * phi s x) := by
  have := (integrable_pow_gauss (b := 1 / (2 * s)) (by positivity) k).div_const
    (Real.sqrt (2 * Real.pi * s))
  refine this.congr (Eventually.of_forall (fun x => ?_))
  simp only [phi]
  rw [mul_div_assoc]
  congr 3
  ring

/-! ### 4. Convergence of moments, polynomial test functions, tightness -/

lemma sigmaSq_pos (r : ℕ) : 0 < sigmaSq r := by
  unfold sigmaSq; have := rho_pos r; have := Kr_pos r; positivity

lemma integrable_mu (r n : ℕ) (g : ℝ → ℝ) : Integrable g (mu r n) := by
  have h0 : (a r n : ENNReal) ≠ 0 := by exact_mod_cast (a_pos r n).ne'
  exact (integral_sum_dirac univ _ g).1.smul_measure (ENNReal.inv_ne_top.2 h0)

/-- **(b) Moment convergence**: for `r ≥ 1` and every `k`,
`∫ x^k dμ_n → ∫ x^k dN(0, σ_r²)`. -/
theorem moment_tendsto {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Tendsto (fun n => ∫ y, y ^ k ∂(mu r n)) atTop (𝓝 (∫ x, x ^ k * phi (sigmaSq r) x)) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [gauss_moment_even (sigmaSq_pos r)]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [mul_zero, pow_zero, Nat.zero_sub, Nat.doubleFactorial, Nat.cast_one, mul_one]
      refine tendsto_const_nhds.congr (fun n => ?_)
      simp
    · have h := tendsto_moment_gaussian hr hm
      rw [factorial_div_eq_doubleFactorial hm] at h
      refine h.congr (fun n => ?_)
      rw [moment_mu, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n)]
  · rw [gauss_moment_odd _ (odd_two_mul_add_one m)]
    refine tendsto_const_nhds.congr (fun n => ?_)
    rw [moment_mu, Mk_odd, Int.cast_zero, zero_div]

/-- **(d) Polynomial test functions**: `∫ f dμ_n → ∫ f dN(0, σ_r²)` for every real polynomial. -/
theorem poly_tendsto {r : ℕ} (hr : 1 ≤ r) (f : Polynomial ℝ) :
    Tendsto (fun n => ∫ y, f.eval y ∂(mu r n)) atTop
      (𝓝 (∫ x, f.eval x * phi (sigmaSq r) x)) := by
  set N := f.natDegree + 1
  have hL : ∀ n, ∫ y, f.eval y ∂(mu r n) = ∑ i ∈ range N, f.coeff i * ∫ y, y ^ i ∂(mu r n) := by
    intro n
    simp only [Polynomial.eval_eq_sum_range]
    rw [integral_finsetSum _ (fun i _ => integrable_mu r n _)]
    exact sum_congr rfl (fun i _ => integral_const_mul _ _)
  have hR : ∫ x, f.eval x * phi (sigmaSq r) x =
      ∑ i ∈ range N, f.coeff i * ∫ x, x ^ i * phi (sigmaSq r) x := by
    simp only [Polynomial.eval_eq_sum_range, sum_mul]
    rw [integral_finsetSum _ (fun i _ => by
      simpa [mul_assoc] using (integrable_pow_phi (sigmaSq_pos r) i).const_mul (f.coeff i))]
    refine sum_congr rfl (fun i _ => ?_)
    rw [← integral_const_mul]
    congr 1; funext x; ring
  simp only [hL, hR]
  exact tendsto_finsetSum _ (fun i _ => (moment_tendsto hr i).const_mul _)

/-- **(c) Tightness**: for every `ε > 0` there is `R` with `μ_n {x : R < |x|} ≤ ε` for all `n`. -/
theorem tight {r : ℕ} (hr : 1 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ n, mu r n {x | R < |x|} ≤ ENNReal.ofReal ε := by
  obtain ⟨B, hB⟩ := (moment_tendsto hr 2).bddAbove_range
  have hB' : ∀ n, ∫ y, y ^ 2 ∂(mu r n) ≤ B := fun n => hB ⟨n, rfl⟩
  have hB0 : 0 ≤ B := le_trans (integral_nonneg (fun y => sq_nonneg y)) (hB' 0)
  set R := Real.sqrt (B / ε) + 1 with hRdef
  have hR : 0 < R := by positivity
  refine ⟨R, hR, fun n => ?_⟩
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε.le]
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := mu r n) (f := fun y => y ^ 2)
    (Eventually.of_forall (fun y => sq_nonneg y)) (integrable_mu r n _) (R ^ 2)
  have hsub : (mu r n).real {x | R < |x|} ≤ (mu r n).real {x | R ^ 2 ≤ x ^ 2} := by
    refine measureReal_mono (fun x hx => ?_)
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have := sq_abs x
    nlinarith [abs_nonneg x]
  have hR2 : B / ε ≤ R ^ 2 := by
    have h1 := Real.sq_sqrt (show 0 ≤ B / ε by positivity)
    have h2 := Real.sqrt_nonneg (B / ε)
    nlinarith
  have hm0 : 0 ≤ (mu r n).real {x | R ^ 2 ≤ x ^ 2} := measureReal_nonneg
  have key : (mu r n).real {x | R ^ 2 ≤ x ^ 2} ≤ ε := by
    have h3 : R ^ 2 * (mu r n).real {x | R ^ 2 ≤ x ^ 2} ≤ B := hM.trans (hB' n)
    have hRp : 0 < R ^ 2 := by positivity
    rw [div_le_iff₀ hε] at hR2
    by_contra hc; push Not at hc
    nlinarith
  exact (measureReal_def _ _ ▸ hsub).trans key

end APEX.Blockade.Gaussian

