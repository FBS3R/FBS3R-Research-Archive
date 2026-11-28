import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Field

/-!
# Power-law mixtures: log-derivatives are mean and variance

`ε(A) = Σ_i C_i A^{s_i}` with a finite nonempty index type `ι`, `C_i > 0`, real exponents `s_i`,
`A > 0`. Weights `p_i(A) = C_i A^{s_i} / ε(A)` (a probability vector, `sum_p`).
With `t = log A` (i.e. `A = e^t`):

* `hasDerivAt_log_eps_exp`: `d/dt log ε(e^t) = Σ p_i(e^t) s_i` (the mean).
* `hasDerivAt_mean_exp`: `d/dt [Σ p_i(e^t) s_i] = Σ p_i s_i² − (Σ p_i s_i)²` (the variance), so the
  second derivative of `log ε(e^t)` is the variance (`hasDerivAt_deriv_log_eps_exp`, stated with `deriv`).
* `variance_eq`, `variance_nonneg`: variance `= Σ p_i (s_i − mean)² ≥ 0` (log-convexity).
* `log_mgf_eq`: `log Σ_i p_i(A) e^{t s_i} = log ε(A e^t) − log ε(A)` (the log-MGF of the
  distribution `p(A)` on `{s_i}` is the shifted `log ε`).

Higher cumulants (k ≥ 3) are not formalised here.
-/

open Real Finset

namespace APEX.Spectral

variable {ι : Type*} [Fintype ι] (C s : ι → ℝ)

/-- `ε(A) = Σ_i C_i A^{s_i}`. -/
noncomputable def eps (A : ℝ) : ℝ := ∑ i, C i * A ^ s i

/-- `p_i(A) = C_i A^{s_i} / ε(A)`. -/
noncomputable def p (A : ℝ) (i : ι) : ℝ := C i * A ^ s i / eps C s A

/-- Mean `Σ p_i s_i`. -/
noncomputable def mean (A : ℝ) : ℝ := ∑ i, p C s A i * s i

/-- Variance `Σ p_i s_i² − (Σ p_i s_i)²`. -/
noncomputable def variance (A : ℝ) : ℝ := ∑ i, p C s A i * s i ^ 2 - mean C s A ^ 2

variable {C s}

lemma eps_pos [Nonempty ι] (hC : ∀ i, 0 < C i) {A : ℝ} (hA : 0 < A) : 0 < eps C s A :=
  Finset.sum_pos (fun i _ => mul_pos (hC i) (rpow_pos_of_pos hA _)) univ_nonempty

lemma sum_p [Nonempty ι] (hC : ∀ i, 0 < C i) {A : ℝ} (hA : 0 < A) : ∑ i, p C s A i = 1 := by
  simp only [p, ← Finset.sum_div]
  exact div_self (eps_pos hC hA).ne'

lemma eps_exp (t : ℝ) : eps C s (exp t) = ∑ i, C i * exp (s i * t) := by
  simp only [eps, ← exp_mul, mul_comm t]

lemma p_exp (t : ℝ) (i : ι) : p C s (exp t) i = C i * exp (s i * t) / ∑ j, C j * exp (s j * t) := by
  rw [p, eps_exp, ← exp_mul, mul_comm t]

lemma hasDerivAt_sum_exp (D : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∑ i, D i * exp (s i * t)) (∑ i, D i * s i * exp (s i * t)) t := by
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h := ((hasDerivAt_id t).const_mul (s i)).exp.const_mul (D i)
  convert h using 1 <;> simp only [id] ; ring

/-- `d/dt log ε(e^t) = Σ p_i(e^t) s_i`. -/
theorem hasDerivAt_log_eps_exp [Nonempty ι] (hC : ∀ i, 0 < C i) (t : ℝ) :
    HasDerivAt (fun t => log (eps C s (exp t))) (mean C s (exp t)) t := by
  have hpos := eps_pos (s := s) hC (exp_pos t)
  simp only [eps_exp] at hpos ⊢
  have h := (hasDerivAt_sum_exp (s := s) C t).log hpos.ne'
  convert h using 1
  simp only [mean, p_exp, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `d/dt [mean(e^t)] = variance(e^t)`. -/
theorem hasDerivAt_mean_exp [Nonempty ι] (hC : ∀ i, 0 < C i) (t : ℝ) :
    HasDerivAt (fun t => mean C s (exp t)) (variance C s (exp t)) t := by
  have hpos := eps_pos (s := s) hC (exp_pos t)
  simp only [eps_exp] at hpos
  have hf := hasDerivAt_sum_exp (s := s) C t
  have hg := hasDerivAt_sum_exp (s := s) (fun i => C i * s i) t
  have h := hg.div hf hpos.ne'
  have hmean : ∀ u, mean C s (exp u) =
      (∑ i, C i * s i * exp (s i * u)) / ∑ i, C i * exp (s i * u) := by
    intro u; simp only [mean, p_exp, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  simp only [hmean]
  convert h using 1
  simp only [variance, hmean, p_exp]
  set f := ∑ i, C i * exp (s i * t)
  have e1 : ∑ x, C x * exp (s x * t) / f * s x ^ 2 = (∑ i, C i * s i * s i * exp (s i * t)) / f := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [e1]
  field_simp
  simp only [mul_comm t]; ring

/-- Second derivative of `log ε(e^t)` is the variance. -/
theorem hasDerivAt_deriv_log_eps_exp [Nonempty ι] (hC : ∀ i, 0 < C i) (t : ℝ) :
    HasDerivAt (deriv fun t => log (eps C s (exp t))) (variance C s (exp t)) t := by
  have : (deriv fun t => log (eps C s (exp t))) = fun t => mean C s (exp t) :=
    funext fun u => (hasDerivAt_log_eps_exp hC u).deriv
  rw [this]; exact hasDerivAt_mean_exp hC t

/-- Variance is the centred second moment. -/
theorem variance_eq [Nonempty ι] (hC : ∀ i, 0 < C i) {A : ℝ} (hA : 0 < A) :
    variance C s A = ∑ i, p C s A i * (s i - mean C s A) ^ 2 := by
  have h1 := sum_p (s := s) hC hA
  have : ∑ i, p C s A i * (s i - mean C s A) ^ 2 =
      ∑ i, p C s A i * s i ^ 2 - 2 * mean C s A * (∑ i, p C s A i * s i)
        + mean C s A ^ 2 * ∑ i, p C s A i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [this, h1, ← mean, variance]; ring

theorem variance_nonneg [Nonempty ι] (hC : ∀ i, 0 < C i) {A : ℝ} (hA : 0 < A) :
    0 ≤ variance C s A := by
  rw [variance_eq hC hA]
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (sq_nonneg _)
  exact div_nonneg (mul_pos (hC i) (rpow_pos_of_pos hA _)).le (eps_pos hC hA).le

/-- `log Σ_i p_i(A) e^{t s_i} = log ε(A e^t) − log ε(A)`. -/
theorem log_mgf_eq [Nonempty ι] (hC : ∀ i, 0 < C i) {A : ℝ} (hA : 0 < A) (t : ℝ) :
    log (∑ i, p C s A i * exp (t * s i)) = log (eps C s (A * exp t)) - log (eps C s A) := by
  have hsum : ∑ i, p C s A i * exp (t * s i) = eps C s (A * exp t) / eps C s A := by
    simp only [p, eps, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_rpow hA.le (exp_pos t).le, ← exp_mul]; ring
  rw [hsum, log_div (eps_pos hC (mul_pos hA (exp_pos t))).ne' (eps_pos hC hA).ne']

end APEX.Spectral

