import APEX.Blockade.Gaussian
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Range-`r` blockade: weak convergence of the spectral measures to `N(0, σ_r²)`

`mu r n = (1/a_{n,r}) ∑_λ δ_{λ/√n}` (eigenvalues of `A_{n,r}`), `phi s` the `N(0,s)` density,
`σ_r² = sigmaSq r = 2ρ^{r+1}/K_r`.

**Main theorem (`weak_limit`).** For `r ≥ 1` and every continuous bounded `g : ℝ → ℝ`,
`∫ g dμ_n → ∫ g(x) φ_{σ_r²}(x) dx`, i.e. `μ_n ⇒ N(0, σ_r²)` weakly.

Proof (hand-made method of moments, no moment-determinacy theorem needed):
* `rem_bound` : `|e^{iy} − ∑_{k<K} (iy)^k/k!| ≤ |y|^K/K!` for all real `y`.
* `charFun_tendsto` : `∫ e^{itx} dμ_n → ∫ e^{itx} φ` — Taylor polynomials converge by
  `moment_tendsto`, remainders are bounded by `|t|^{2L} m_{2L}/(2L)!`, and
  `|t|^{2L} ((2L−1)!! σ^{2L} + 1)/(2L)! → 0` (`coef_tendsto`).
* `trig_tendsto` : `∫ q(sin(cx)) dμ_n → ∫ q(sin(cx)) φ` for real polynomials `q`
  (`sin(cx)^j` is a combination of `e^{i k c x}`).
* `exists_trig_approx` : with `c = π/(2R)`, Weierstrass applied to `g(arcsin(y)/c)` on `[−1,1]`
  gives `F = q(sin(c·))` with `|F − g| ≤ δ` on `[−R,R]` and `|F| ≤ M + δ` everywhere.
* `weak_limit` : `|g − F| ≤ δ + (2M+δ) x²/R²` pointwise, and second moments are uniformly
  bounded; conclude with the `ε/3` lemma `tendsto_of_approx`.
-/

namespace APEX.Blockade.WeakLimit

open Finset Filter Topology MeasureTheory Complex
open APEX.Blockade.Asymptotics APEX.Blockade.Gaussian

/-! ### 1. Taylor bound for `e^{iy}` -/

/-- Taylor polynomial of `e^{i y}` of order `K`. -/
noncomputable def tp (K : ℕ) (y : ℝ) : ℂ := ∑ k ∈ range K, (I * y) ^ k / (k.factorial : ℂ)

/-- Remainder. -/
noncomputable def rem (K : ℕ) (y : ℝ) : ℂ := exp (I * y) - tp K y

lemma hasDerivAt_rem (K : ℕ) (y : ℝ) : HasDerivAt (rem (K + 1)) (I * rem K y) y := by
  have hc : HasDerivAt (fun w : ℂ => exp (I * w) - ∑ k ∈ range (K + 1), (I * w) ^ k / (k.factorial : ℂ))
      (I * (exp (I * y) - ∑ k ∈ range K, (I * y) ^ k / (k.factorial : ℂ))) (y : ℂ) := by
    have h1 : HasDerivAt (fun w : ℂ => exp (I * w)) (exp (I * y) * I) (y : ℂ) := by
      have := ((hasDerivAt_id (y : ℂ)).const_mul I).cexp
      simpa using this
    have h2 : HasDerivAt (fun w : ℂ => ∑ k ∈ range (K + 1), (I * w) ^ k / (k.factorial : ℂ))
        (∑ k ∈ range (K + 1), (k : ℂ) * (I * y) ^ (k - 1) * I / (k.factorial : ℂ)) (y : ℂ) := by
      apply HasDerivAt.fun_sum
      intro k _
      have := (((hasDerivAt_id (y : ℂ)).const_mul I).pow k).div_const (k.factorial : ℂ)
      simpa using this
    convert h1.sub h2 using 1
    rw [sum_range_succ', mul_sub, mul_sum]
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
    congr 1
    · ring
    · refine sum_congr rfl (fun k _ => ?_)
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast k.succ_ne_zero
      field_simp
  exact hc.comp_ofReal

lemma rem_zero_at (K : ℕ) : rem (K + 1) 0 = 0 := by
  simp [rem, tp, sum_range_succ']

lemma rem_bound_nonneg : ∀ (K : ℕ) {y : ℝ}, 0 ≤ y → ‖rem K y‖ ≤ y ^ K / K.factorial
  | 0, y, _ => by
    simp [rem, tp, mul_comm I, Complex.norm_exp_ofReal_mul_I]
  | K + 1, y, hy => by
    have ih := fun s (hs : 0 ≤ s) => rem_bound_nonneg K hs
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := rem (K + 1)) (a := 0) (b := y)
      (f' := fun s => I * rem K s) (B := fun s => s ^ (K + 1) / (K + 1).factorial)
      (B' := fun s => s ^ K / K.factorial) ?_ ?_ ?_ ?_ ?_ ⟨hy, le_rfl⟩
    · exact fun s _ => (hasDerivAt_rem K s).continuousAt.continuousWithinAt
    · exact fun s _ => (hasDerivAt_rem K s).hasDerivWithinAt
    · simp [rem_zero_at]
    · intro s
      have := (hasDerivAt_pow (K + 1) s).div_const ((K + 1).factorial : ℝ)
      convert this using 1
      rw [Nat.factorial_succ]; push_cast
      have : (K.factorial : ℝ) ≠ 0 := by exact_mod_cast K.factorial_ne_zero
      field_simp
    · intro s hs
      rw [norm_mul, Complex.norm_I, one_mul]
      exact ih s hs.1

lemma rem_neg (K : ℕ) (y : ℝ) : rem K (-y) = (starRingEnd ℂ) (rem K y) := by
  simp only [rem, tp, map_sub, map_sum, map_div₀, map_pow, map_mul, Complex.conj_I, Complex.conj_ofReal,
    map_natCast, ← Complex.exp_conj]
  push_cast
  congr 1
  · congr 1; ring
  · refine sum_congr rfl (fun k _ => ?_); congr 2; ring

/-- `‖e^{iy} − ∑_{k<K} (iy)^k/k!‖ ≤ |y|^K / K!`. -/
theorem rem_bound (K : ℕ) (y : ℝ) : ‖rem K y‖ ≤ |y| ^ K / K.factorial := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact rem_bound_nonneg K hy
  · have h := rem_bound_nonneg K (neg_nonneg.2 hy.le)
    have e : rem K y = (starRingEnd ℂ) (rem K (-y)) := by rw [← rem_neg, neg_neg]
    rw [e, Complex.norm_conj, abs_of_neg hy]
    exact h

/-! ### 2. Generalities -/

/-- An `ε/3` lemma: approximation by convergent sequences with uniformly small error. -/
theorem tendsto_of_approx {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} {l : E}
    (h : ∀ ε > 0, ∃ v : ℕ → E, ∃ w : E, Tendsto v atTop (𝓝 w) ∧
      (∀ᶠ n in atTop, ‖u n - v n‖ ≤ ε) ∧ ‖l - w‖ ≤ ε) : Tendsto u atTop (𝓝 l) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨v, w, hv, hu, hl⟩ := h (ε / 4) (by positivity)
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hv (ε / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hu
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have a1 := hN1 n (le_of_max_le_left hn)
  have a2 := hN2 n (le_of_max_le_right hn)
  rw [dist_eq_norm] at a1 ⊢
  calc ‖u n - l‖ = ‖(u n - v n) + (v n - w) + (w - l)‖ := by congr 1; abel
    _ ≤ ‖u n - v n‖ + ‖v n - w‖ + ‖w - l‖ := norm_add₃_le
    _ < ε := by rw [norm_sub_rev w]; linarith

lemma integral_sum_dirac' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) (g : ℝ → E) :
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

lemma integrable_mu' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (r n : ℕ) (g : ℝ → E) : Integrable g (mu r n) := by
  have h0 : (a r n : ENNReal) ≠ 0 := by exact_mod_cast (a_pos r n).ne'
  exact (integral_sum_dirac' univ _ g).1.smul_measure (ENNReal.inv_ne_top.2 h0)

lemma continuous_phi (s : ℝ) : Continuous (phi s) := by
  unfold phi; fun_prop

lemma phi_nonneg {s : ℝ} (x : ℝ) : 0 ≤ phi s x := by
  unfold phi; positivity

lemma integrable_phi {s : ℝ} (hs : 0 < s) : Integrable (phi s) := by
  simpa using integrable_pow_phi hs 0

/-- Bounded continuous functions are integrable against the Gaussian density. -/
lemma integrable_bdd_mul_phi {s : ℝ} (hs : 0 < s) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} (hg : Continuous g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) :
    Integrable (fun x => phi s x • g x) := by
  refine ((integrable_phi hs).const_mul M).mono' ((continuous_phi s).smul hg).aestronglyMeasurable
    (Eventually.of_forall (fun x => ?_))
  rw [norm_smul, Real.norm_of_nonneg (phi_nonneg x), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM x) (phi_nonneg x)

lemma gauss_moment_le {s : ℝ} (hs : 0 < s) (m : ℕ) :
    0 ≤ ∫ x, x ^ (2 * m) * phi s x := by
  rw [gauss_moment_even hs]; positivity

/-! ### 3. Convergence of the characteristic functions -/

/-- `e^{itx}`. -/
noncomputable def ex (t x : ℝ) : ℂ := exp (I * ((t * x : ℝ) : ℂ))

lemma norm_ex (t x : ℝ) : ‖ex t x‖ = 1 := by
  rw [ex, mul_comm, Complex.norm_exp_ofReal_mul_I]

lemma continuous_ex (t : ℝ) : Continuous (ex t) := by unfold ex; fun_prop

lemma tp_eq (K : ℕ) (t x : ℝ) :
    tp K (t * x) = ∑ k ∈ range K, (I * t) ^ k / (k.factorial : ℂ) * ((x ^ k : ℝ) : ℂ) := by
  unfold tp
  refine sum_congr rfl (fun k _ => ?_)
  push_cast; ring

lemma continuous_tp (K : ℕ) (t : ℝ) : Continuous (fun x : ℝ => tp K (t * x)) := by
  simp only [tp_eq]; fun_prop

lemma tp_tendsto {r : ℕ} (hr : 1 ≤ r) (K : ℕ) (t : ℝ) :
    Tendsto (fun n => ∫ x, tp K (t * x) ∂(mu r n)) atTop
      (𝓝 (∫ x, phi (sigmaSq r) x • tp K (t * x))) := by
  have hs := sigmaSq_pos r
  have hL : ∀ n, ∫ x, tp K (t * x) ∂(mu r n) =
      ∑ k ∈ range K, (I * t) ^ k / (k.factorial : ℂ) * ((∫ x, x ^ k ∂(mu r n) : ℝ) : ℂ) := by
    intro n
    simp only [tp_eq]
    rw [integral_finsetSum _ (fun k _ => integrable_mu' r n _)]
    refine sum_congr rfl (fun k _ => ?_)
    rw [integral_const_mul]; congr 1; exact integral_ofReal
  have hR : ∫ x, phi (sigmaSq r) x • tp K (t * x) =
      ∑ k ∈ range K, (I * t) ^ k / (k.factorial : ℂ) *
        ((∫ x, x ^ k * phi (sigmaSq r) x : ℝ) : ℂ) := by
    have e : ∀ x, phi (sigmaSq r) x • tp K (t * x) = ∑ k ∈ range K,
        (I * t) ^ k / (k.factorial : ℂ) * ((x ^ k * phi (sigmaSq r) x : ℝ) : ℂ) := by
      intro x
      rw [tp_eq, Finset.smul_sum]
      refine sum_congr rfl (fun k _ => ?_)
      rw [Complex.real_smul]; push_cast; ring
    simp only [e]
    rw [integral_finsetSum _ (fun k _ => by
      have := ((integrable_pow_phi hs k).ofReal (𝕜 := ℂ)).const_mul ((I * t) ^ k / (k.factorial : ℂ))
      exact this)]
    refine sum_congr rfl (fun k _ => ?_)
    rw [integral_const_mul]; congr 1; exact integral_ofReal
  simp only [hL, hR]
  exact tendsto_finsetSum _ (fun k _ =>
    (((Complex.continuous_ofReal.tendsto _).comp (moment_tendsto hr k))).const_mul _)

lemma ex_eq (K : ℕ) (t x : ℝ) : ex t x = tp K (t * x) + rem K (t * x) := by
  simp [ex, rem]

lemma continuous_rem (K : ℕ) (t : ℝ) : Continuous (fun x : ℝ => rem K (t * x)) := by
  have : (fun x : ℝ => rem K (t * x)) = fun x => ex t x - tp K (t * x) := by
    funext x; rw [ex_eq K]; ring
  rw [this]; exact (continuous_ex t).sub (continuous_tp K t)

lemma rem_bound' (L : ℕ) (t x : ℝ) :
    ‖rem (2 * L) (t * x)‖ ≤ |t| ^ (2 * L) / ((2 * L).factorial : ℝ) * x ^ (2 * L) := by
  refine (rem_bound _ _).trans (le_of_eq ?_)
  rw [abs_mul, mul_pow, pow_mul (|x|), sq_abs, ← pow_mul]
  ring

/-- `|t|^{2L} (M_{2L} + 1) / (2L)! → 0`. -/
lemma coef_tendsto (s t : ℝ) (hs : 0 < s) :
    Tendsto (fun L : ℕ => |t| ^ (2 * L) / ((2 * L).factorial : ℝ) *
      ((∫ x, x ^ (2 * L) * phi s x) + 1)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun L : ℕ => 2 * L) atTop atTop :=
    tendsto_atTop_mono (fun L => by simp only [id]; omega) tendsto_id
  have hA := (FloorSemiring.tendsto_pow_div_factorial_atTop (|t|)).comp h2
  have hB := FloorSemiring.tendsto_pow_div_factorial_atTop (t ^ 2 * s / 2)
  have hC := hB.add hA
  rw [add_zero] at hC
  refine hC.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  simp only [Function.comp, gauss_moment_even hs]
  have hf := factorial_div_eq_doubleFactorial hL
  have h1 : (L.factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((2 * L).factorial : ℝ) ≠ 0 := by positivity
  rw [← hf, mul_add, mul_one]
  congr 1
  rw [div_pow, mul_pow, ← pow_mul, pow_mul (|t|), sq_abs]
  field_simp
  rw [pow_mul]

/-- **Characteristic functions converge**: `∫ e^{itx} dμ_n → ∫ e^{itx} φ_{σ_r²}(x) dx`. -/
theorem charFun_tendsto {r : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    Tendsto (fun n => ∫ x, ex t x ∂(mu r n)) atTop (𝓝 (∫ x, phi (sigmaSq r) x • ex t x)) := by
  have hs := sigmaSq_pos r
  apply tendsto_of_approx
  intro ε hε
  obtain ⟨L, hLε⟩ := ((coef_tendsto _ t hs).eventually (ge_mem_nhds hε)).exists
  set c := |t| ^ (2 * L) / ((2 * L).factorial : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  set Mg := ∫ x, x ^ (2 * L) * phi (sigmaSq r) x
  have hMg := gauss_moment_le hs L
  refine ⟨fun n => ∫ x, tp (2 * L) (t * x) ∂(mu r n), ∫ x, phi (sigmaSq r) x • tp (2 * L) (t * x),
    tp_tendsto hr _ t, ?_, ?_⟩
  · have hm := moment_tendsto hr (2 * L)
    filter_upwards [(hm.eventually (gt_mem_nhds (show Mg < Mg + 1 by linarith)))] with n hn
    rw [← integral_sub (integrable_mu' r n _) (integrable_mu' r n _)]
    have e : ∀ x, ex t x - tp (2 * L) (t * x) = rem (2 * L) (t * x) := fun x => by
      rw [ex_eq (2 * L)]; ring
    simp only [e]
    refine (norm_integral_le_of_norm_le ((integrable_mu r n _).const_mul c)
      (Eventually.of_forall (fun x => rem_bound' L t x))).trans ?_
    rw [integral_const_mul]
    calc c * ∫ x, x ^ (2 * L) ∂(mu r n) ≤ c * (Mg + 1) :=
          mul_le_mul_of_nonneg_left hn.le hc0
      _ ≤ ε := hLε
  · have hex := integrable_bdd_mul_phi hs (continuous_ex t) (fun x => (norm_ex t x).le)
    have hrem : Integrable (fun x => phi (sigmaSq r) x • rem (2 * L) (t * x)) := by
      refine ((integrable_pow_phi hs (2 * L)).const_mul c).mono'
        ((continuous_phi _).smul (continuous_rem _ t)).aestronglyMeasurable
        (Eventually.of_forall (fun x => ?_))
      rw [norm_smul, Real.norm_of_nonneg (phi_nonneg x)]
      have := mul_le_mul_of_nonneg_left (rem_bound' L t x) (phi_nonneg (s := sigmaSq r) x)
      linarith [show phi (sigmaSq r) x * (c * x ^ (2 * L)) = c * (x ^ (2 * L) * phi (sigmaSq r) x)
        by ring]
    have htp : Integrable (fun x => phi (sigmaSq r) x • tp (2 * L) (t * x)) := by
      refine (hex.sub hrem).congr (Eventually.of_forall (fun x => ?_))
      simp only [Pi.sub_apply]
      rw [ex_eq (2 * L) t x, smul_add]; abel
    rw [← integral_sub hex htp]
    have e : ∀ x, phi (sigmaSq r) x • ex t x - phi (sigmaSq r) x • tp (2 * L) (t * x) =
        phi (sigmaSq r) x • rem (2 * L) (t * x) := fun x => by
      rw [ex_eq (2 * L), smul_add]; abel
    simp only [e]
    refine (norm_integral_le_of_norm_le ((integrable_pow_phi hs (2 * L)).const_mul c)
      (Eventually.of_forall (fun x => ?_))).trans ?_
    · rw [norm_smul, Real.norm_of_nonneg (phi_nonneg x)]
      have := mul_le_mul_of_nonneg_left (rem_bound' L t x) (phi_nonneg (s := sigmaSq r) x)
      linarith [show phi (sigmaSq r) x * (c * x ^ (2 * L)) = c * (x ^ (2 * L) * phi (sigmaSq r) x)
        by ring]
    · rw [integral_const_mul]
      nlinarith

/-! ### 4. Trigonometric test functions `q(sin(cx))` -/

lemma sin_eq_ex (c x : ℝ) : ((Real.sin (c * x) : ℝ) : ℂ) = (ex c x - ex (-c) x) / (2 * I) := by
  rw [Complex.ofReal_sin, Complex.sin, ex, ex]
  have hI : (2 * I) ≠ 0 := by simp
  field_simp
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring_nf

lemma ex_pow_mul (c x : ℝ) (j l : ℕ) (hl : l ≤ j) :
    ex c x ^ l * ex (-c) x ^ (j - l) = ex ((2 * (l : ℝ) - j) * c) x := by
  unfold ex
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast [Nat.cast_sub hl]
  ring

lemma sin_pow_eq (c x : ℝ) (j : ℕ) : ((Real.sin (c * x) ^ j : ℝ) : ℂ) =
    ∑ l ∈ range (j + 1), ((2 * I) ^ j)⁻¹ * (j.choose l : ℂ) * (-1) ^ (j - l) *
      ex ((2 * (l : ℝ) - j) * c) x := by
  rw [Complex.ofReal_pow, sin_eq_ex, div_pow, sub_eq_add_neg, add_pow, div_eq_inv_mul, mul_sum]
  refine sum_congr rfl (fun l hl => ?_)
  have hl' : l ≤ j := by have := mem_range.1 hl; omega
  rw [← ex_pow_mul c x j l hl', neg_pow]
  ring

/-- Trigonometric test functions: `∫ q(sin(cx)) dμ_n → ∫ q(sin(cx)) φ_{σ_r²}`. -/
theorem trig_tendsto {r : ℕ} (hr : 1 ≤ r) (q : Polynomial ℝ) (c : ℝ) :
    Tendsto (fun n => ∫ x, q.eval (Real.sin (c * x)) ∂(mu r n)) atTop
      (𝓝 (∫ x, q.eval (Real.sin (c * x)) * phi (sigmaSq r) x)) := by
  have hs := sigmaSq_pos r
  set N := q.natDegree + 1
  set γ : ℕ → ℕ → ℂ := fun j l => (q.coeff j : ℂ) * (((2 * I) ^ j)⁻¹ * (j.choose l : ℂ) * (-1) ^ (j - l))
  set τ : ℕ → ℕ → ℝ := fun j l => (2 * (l : ℝ) - j) * c
  have key : ∀ x : ℝ, ((q.eval (Real.sin (c * x)) : ℝ) : ℂ) =
      ∑ j ∈ range N, ∑ l ∈ range (j + 1), γ j l * ex (τ j l) x := by
    intro x
    rw [Polynomial.eval_eq_sum_range, Complex.ofReal_sum]
    refine sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_mul, sin_pow_eq, mul_sum]
    refine sum_congr rfl (fun l _ => ?_)
    simp only [γ, τ]; ring
  have hL : ∀ n, ((∫ x, q.eval (Real.sin (c * x)) ∂(mu r n) : ℝ) : ℂ) =
      ∑ j ∈ range N, ∑ l ∈ range (j + 1), γ j l * ∫ x, ex (τ j l) x ∂(mu r n) := by
    intro n
    rw [← integral_complex_ofReal]
    simp only [key]
    rw [integral_finsetSum _ (fun j _ => integrable_mu' r n _)]
    refine sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum _ (fun l _ => integrable_mu' r n _)]
    exact sum_congr rfl (fun l _ => integral_const_mul _ _)
  have hR : ((∫ x, q.eval (Real.sin (c * x)) * phi (sigmaSq r) x : ℝ) : ℂ) =
      ∑ j ∈ range N, ∑ l ∈ range (j + 1), γ j l * ∫ x, phi (sigmaSq r) x • ex (τ j l) x := by
    rw [← integral_complex_ofReal]
    have e : ∀ x, (((q.eval (Real.sin (c * x)) * phi (sigmaSq r) x : ℝ)) : ℂ) =
        ∑ j ∈ range N, ∑ l ∈ range (j + 1), γ j l * (phi (sigmaSq r) x • ex (τ j l) x) := by
      intro x
      rw [Complex.ofReal_mul, key, sum_mul]
      refine sum_congr rfl (fun j _ => ?_)
      rw [sum_mul]
      refine sum_congr rfl (fun l _ => ?_)
      rw [Complex.real_smul]; ring
    simp only [e]
    have hi : ∀ j l, Integrable (fun x => γ j l * (phi (sigmaSq r) x • ex (τ j l) x)) := fun j l =>
      (integrable_bdd_mul_phi hs (continuous_ex _) (fun x => (norm_ex _ x).le)).const_mul _
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ => hi j l))]
    refine sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum _ (fun l _ => hi j l)]
    exact sum_congr rfl (fun l _ => integral_const_mul _ _)
  have hC : Tendsto (fun n => ((∫ x, q.eval (Real.sin (c * x)) ∂(mu r n) : ℝ) : ℂ)) atTop
      (𝓝 ((∫ x, q.eval (Real.sin (c * x)) * phi (sigmaSq r) x : ℝ) : ℂ)) := by
    simp only [hL, hR]
    exact tendsto_finsetSum _ (fun j _ => tendsto_finsetSum _ (fun l _ =>
      (charFun_tendsto hr _).const_mul _))
  have := (Complex.continuous_re.tendsto _).comp hC
  simpa [Function.comp_def] using this

/-! ### 5. Weak convergence -/

/-- Uniform approximation on `[−R, R]` by `q(sin(cx))`, with a global bound. -/
lemma exists_trig_approx {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    {R : ℝ} (hR : 0 < R) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (q : Polynomial ℝ) (c : ℝ), (∀ x, |q.eval (Real.sin (c * x))| ≤ M + δ) ∧
      (∀ x, |x| ≤ R → |q.eval (Real.sin (c * x)) - g x| ≤ δ) := by
  set c := Real.pi / (2 * R) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun y => g (Real.arcsin y / c))
    (by fun_prop) δ hδ
  refine ⟨q, c, fun x => ?_, fun x hx => ?_⟩
  · have hy : Real.sin (c * x) ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have h1 := hq _ hy
    have h2 := hM (Real.arcsin (Real.sin (c * x)) / c)
    have := abs_sub_abs_le_abs_sub (q.eval (Real.sin (c * x))) (g (Real.arcsin (Real.sin (c * x)) / c))
    linarith
  · have hy : Real.sin (c * x) ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have h1 := hq _ hy
    have hcx : |c * x| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos hc0, hc]
      have : Real.pi / (2 * R) * |x| ≤ Real.pi / (2 * R) * R :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      calc Real.pi / (2 * R) * |x| ≤ Real.pi / (2 * R) * R := this
        _ = Real.pi / 2 := by field_simp
    have ha : Real.arcsin (Real.sin (c * x)) = c * x :=
      Real.arcsin_sin (by linarith [neg_abs_le (c * x)]) (by linarith [le_abs_self (c * x)])
    rw [ha, mul_div_cancel_left₀ _ hc0.ne'] at h1
    exact h1.le

/-- **Weak convergence of the spectral measures to `N(0, σ_r²)`**: for `r ≥ 1` and every bounded
continuous `g`, `∫ g dμ_n → ∫ g φ_{σ_r²}`. -/
theorem weak_limit {r : ℕ} (hr : 1 ≤ r) {g : ℝ → ℝ} (hg : Continuous g) (hbd : ∃ M, ∀ x, |g x| ≤ M) :
    Tendsto (fun n => ∫ x, g x ∂(mu r n)) atTop (𝓝 (∫ x, g x * phi (sigmaSq r) x)) := by
  obtain ⟨M, hM⟩ := hbd
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hs := sigmaSq_pos r
  set s := sigmaSq r
  have hs2 : ∫ x, x ^ 2 * phi s x = s := by
    have := gauss_moment_even hs 1; simpa using this
  have hφ1 : ∫ x, phi s x = 1 := by
    have := gauss_moment_even hs 0; simpa using this
  obtain ⟨B0, hB0⟩ := (moment_tendsto hr 2).bddAbove_range
  set B := |B0| + s
  have hBn : ∀ n, ∫ x, x ^ 2 ∂(mu r n) ≤ B := fun n =>
    (hB0 ⟨n, rfl⟩).trans (by linarith [le_abs_self B0])
  have hBs : s ≤ B := by linarith [abs_nonneg B0]
  have hB : 0 ≤ B := by linarith
  apply tendsto_of_approx
  intro ε hε
  set δ := ε / 2
  have hδ : 0 < δ := by positivity
  have hδe : δ + δ = ε := by simp only [δ]; ring
  set R := Real.sqrt ((2 * M + δ) * B / δ) + 1
  have hR : 0 < R := by positivity
  set K := (2 * M + δ) / R ^ 2
  have hK0 : 0 ≤ K := by positivity
  have hKB : K * B ≤ δ := by
    have h1 := Real.sq_sqrt (show 0 ≤ (2 * M + δ) * B / δ by positivity)
    have h2 := Real.sqrt_nonneg ((2 * M + δ) * B / δ)
    have hR2 : (2 * M + δ) * B / δ ≤ R ^ 2 := by nlinarith
    rw [div_le_iff₀ hδ] at hR2
    have hRp : 0 < R ^ 2 := by positivity
    show (2 * M + δ) / R ^ 2 * B ≤ δ
    rw [div_mul_eq_mul_div, div_le_iff₀ hRp]
    linarith
  obtain ⟨q, c, hq1, hq2⟩ := exists_trig_approx hg hM hR hδ
  set F := fun x => q.eval (Real.sin (c * x))
  have hF : Continuous F := q.continuous.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  -- pointwise bound
  have hpt : ∀ x, ‖g x - F x‖ ≤ δ + K * x ^ 2 := by
    intro x
    rw [Real.norm_eq_abs]
    rcases le_or_gt (|x|) R with hx | hx
    · have := hq2 x hx
      rw [abs_sub_comm] at this
      nlinarith [sq_nonneg x]
    · have hx2 : R ^ 2 ≤ x ^ 2 := by
        have := sq_abs x
        nlinarith [abs_nonneg x]
      have hRp : 0 < R ^ 2 := by positivity
      have h1 : 2 * M + δ ≤ K * x ^ 2 := by
        show 2 * M + δ ≤ (2 * M + δ) / R ^ 2 * x ^ 2
        rw [div_mul_eq_mul_div, le_div_iff₀ hRp]
        nlinarith
      have := abs_sub (g x) (F x)
      have := hM x
      have := hq1 x
      linarith
  refine ⟨fun n => ∫ x, F x ∂(mu r n), ∫ x, F x * phi s x, trig_tendsto hr q c, ?_, ?_⟩
  · refine Eventually.of_forall (fun n => ?_)
    rw [← integral_sub (integrable_mu r n _) (integrable_mu r n _)]
    refine (norm_integral_le_of_norm_le (integrable_mu r n (fun x => δ + K * x ^ 2))
      (Eventually.of_forall hpt)).trans ?_
    rw [integral_add (integrable_mu r n _) (integrable_mu r n _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have := mul_le_mul_of_nonneg_left (hBn n) hK0
    linarith
  · have hgi : Integrable (fun x => g x * phi s x) := by
      simpa [smul_eq_mul, mul_comm] using integrable_bdd_mul_phi hs hg (M := M) (fun x => by
        rw [Real.norm_eq_abs]; exact hM x)
    have hFi : Integrable (fun x => F x * phi s x) := by
      simpa [smul_eq_mul, mul_comm] using integrable_bdd_mul_phi hs hF (M := M + δ) (fun x => by
        rw [Real.norm_eq_abs]; exact hq1 x)
    rw [← integral_sub hgi hFi]
    have hbi : Integrable (fun x => δ * phi s x + K * (x ^ 2 * phi s x)) :=
      ((integrable_phi hs).const_mul δ).add ((integrable_pow_phi hs 2).const_mul K)
    refine (norm_integral_le_of_norm_le hbi (Eventually.of_forall (fun x => ?_))).trans ?_
    · rw [← sub_mul, norm_mul, Real.norm_of_nonneg (phi_nonneg x)]
      have := mul_le_mul_of_nonneg_right (hpt x) (phi_nonneg (s := s) x)
      linarith [show (δ + K * x ^ 2) * phi s x = δ * phi s x + K * (x ^ 2 * phi s x) by ring]
    · rw [integral_add ((integrable_phi hs).const_mul δ) ((integrable_pow_phi hs 2).const_mul K),
        integral_const_mul, integral_const_mul, hφ1, hs2]
      have := mul_le_mul_of_nonneg_left hBs hK0
      linarith

end APEX.Blockade.WeakLimit

