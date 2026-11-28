import APEX.Blockade.Root
import APEX.Blockade.General.Residue
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Range-`r` blockade: exact asymptotics of the spectral moments

`A_{n,r} = adjMat r n` (adjacency matrix of the range-`r` constrained hypercube),
`Mk k r n = Tr A_{n,r}^k`, `a r n = dim`, `ρ = rho r` the root of `1 − z − z^{r+1}` in `(0,1)`,
`K_r = ρ + (r+1)ρ^{r+1}`, `σ_r² = sigmaSq r = 2ρ^{r+1}/K_r`.

Main results (for `r ≥ 1`, `m ≥ 1`):
* `tendsto_moment` : `Tr(A_{n,r}^{2m}) · ρⁿ / n^m → (2m)! ρ^{(r+1)m−r} / (m! K_r^{m+1})`.
* `tendsto_moment_normalised` : `Tr(A_{n,r}^{2m}) / (a_{n,r} n^m) → ((2m)!/m!) (ρ^{r+1}/K_r)^m`.
* `tendsto_moment_gaussian` : the same limit written as `((2m)!/(m! 2^m)) σ_r^{2m}`, and
  `factorial_div_eq_doubleFactorial` : `(2m)!/(m! 2^m) = (2m−1)!!` — i.e. the normalised moments
  of the spectral measure of `A_{n,r}/√n` converge to those of `N(0, σ_r²)`.
* `Mk_odd` : `Tr A_{n,r}^{2m+1} = 0` for all `r, n, m` (bipartite: conjugation by `(−1)^{#ones}`).

Route.
* `cZ r n = [zⁿ] 1/D_r` (`Ser_mul_D`), `cm r m n = [zⁿ] D_r^{−(m+1)}`, `cm_succ` (convolution).
* `v_zero_tendsto` : `cZ r n · ρⁿ → 1/K_r` (averaging recurrence of `Root.lean`).
* `weighted_cesaro`, `conv_tendsto` (general real lemmas): if `x n / C(n+m,m) → A` and
  `y n → B` then `(∑_{k≤n} x_k y_{n−k}) / C(n+m+1,m+1) → AB`.
* `v_tendsto_bc` / `v_tendsto` : `[zⁿ] D_r^{−(m+1)} · ρⁿ / C(n+m,m) → K_r^{−(m+1)}`, hence
  `· / n^m → 1/(m! K_r^{m+1})` (pole of order `m+1`).
* `Mk_eq_sum` (reduction lemma): from `(∑ Tr A^{2m} zⁿ) D_r^{m+1} = P`,
  `Tr A_{n,r}^{2m} = ∑_{i≤d} P_i [z^{n−i}] D_r^{−(m+1)}` for `n ≥ deg P`; thus the limit is
  `P(ρ)/(m! K_r^{m+1})`, and `aeval_numerator` : `P(ρ) = (2m)! ρ^{(r+1)m−r}` by `moment_residue`.
-/

namespace APEX.Blockade.Asymptotics

open Finset Filter Topology

/-! ### 1. Coefficients of `1/D_r` and of `1/D_r^{m+1}` -/

/-- `cZ r n = [zⁿ] 1/(1 − z − z^{r+1})`. -/
def cZ (r : ℕ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => cZ r n + if r ≤ n then cZ r (n - r) else 0
termination_by n => n
decreasing_by all_goals omega

lemma cZ_zero (r : ℕ) : cZ r 0 = 1 := by rw [cZ]

lemma cZ_succ (r n : ℕ) : cZ r (n + 1) = cZ r n + if r ≤ n then cZ r (n - r) else 0 := by
  rw [cZ]

lemma cZ_of_le (r : ℕ) : ∀ i, i ≤ r → cZ r i = 1
  | 0, _ => cZ_zero r
  | i + 1, h => by
    rw [cZ_succ, cZ_of_le r i (by omega)]
    simp [show ¬ r ≤ i by omega]

lemma cZ_rec (r n : ℕ) : cZ r (n + r + 1) = cZ r (n + r) + cZ r n := by
  rw [cZ_succ, Nat.add_sub_cancel]
  simp

/-- The power series `∑ cZ r n zⁿ`. -/
noncomputable def Ser (r : ℕ) : PowerSeries ℤ := PowerSeries.mk (cZ r)

theorem Ser_mul_D (r : ℕ) : Ser r * (1 - PowerSeries.X - PowerSeries.X ^ (r + 1)) = 1 := by
  have e : Ser r * (1 - PowerSeries.X - PowerSeries.X ^ (r + 1)) =
      Ser r - Ser r * PowerSeries.X ^ 1 - Ser r * PowerSeries.X ^ (r + 1) := by ring
  rw [e]
  ext n
  rw [map_sub, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', Ser,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases n with _ | n
  · simp [cZ_zero]
  · rw [cZ_succ]
    split_ifs <;> simp_all [Nat.add_sub_add_right] <;> omega

/-- `cm r m n = [zⁿ] 1/D_r^{m+1}`. -/
noncomputable def cm (r m n : ℕ) : ℤ := PowerSeries.coeff n (Ser r ^ (m + 1))

lemma cm_zero (r n : ℕ) : cm r 0 n = cZ r n := by
  rw [cm, zero_add, pow_one, Ser, PowerSeries.coeff_mk]

lemma cm_succ (r m n : ℕ) :
    cm r (m + 1) n = ∑ k ∈ range (n + 1), cm r m k * cZ r (n - k) := by
  rw [cm, pow_succ, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (Ser r ^ (m + 1)) * PowerSeries.coeff j (Ser r))]
  refine sum_congr rfl (fun k _ => ?_)
  rw [cm, Ser, PowerSeries.coeff_mk]

/-- `Tr A_{n,r}^{2m} = ∑_{i ≤ d} P_i · [z^{n−i}] D_r^{−(m+1)}` for `n ≥ d`, `P` the numerator. -/
theorem Mk_eq_sum {r m : ℕ} (P : Polynomial ℤ) {d : ℕ} (hd : P.natDegree ≤ d)
    (hP : PowerSeries.mk (fun n => Mk (2 * m) r n) *
      (1 - PowerSeries.X - PowerSeries.X ^ (r + 1)) ^ (m + 1) = (P : PowerSeries ℤ))
    {n : ℕ} (hn : d ≤ n) :
    Mk (2 * m) r n = ∑ i ∈ range (d + 1), P.coeff i * cm r m (n - i) := by
  have hS : PowerSeries.mk (fun n => Mk (2 * m) r n) = (P : PowerSeries ℤ) * Ser r ^ (m + 1) := by
    rw [← hP, mul_assoc, ← mul_pow, mul_comm _ (Ser r), Ser_mul_D, one_pow, mul_one]
  have := congrArg (PowerSeries.coeff n) hS
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (P : PowerSeries ℤ) * PowerSeries.coeff j (Ser r ^ (m + 1)))]
    at this
  rw [this]
  simp only [Polynomial.coeff_coe, ← cm.eq_1]
  symm
  apply Finset.sum_subset
  · intro i hi; simp only [mem_range] at hi ⊢; omega
  · intro i hi hi'
    simp only [mem_range] at hi hi'
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

/-! ### 2. Real-analysis lemmas: weighted Cesàro and convolution with a convergent sequence -/

/-- `s m k = C(k+m, m)` as a real number. -/
noncomputable def bc (m k : ℕ) : ℝ := ((k + m).choose m : ℕ)

lemma bc_pos (m k : ℕ) : 0 < bc m k := by
  unfold bc; exact_mod_cast Nat.choose_pos (by omega)

lemma bc_mono (m : ℕ) {k n : ℕ} (h : k ≤ n) : bc m k ≤ bc m n := by
  unfold bc; exact_mod_cast Nat.choose_le_choose m (by omega)

/-- Hockey stick: `∑_{k ≤ n} C(k+m, m) = C(n+m+1, m+1)`. -/
lemma hockey (m : ℕ) : ∀ n, ∑ k ∈ range (n + 1), bc m k = bc (m + 1) n
  | 0 => by simp [bc]
  | n + 1 => by
    rw [sum_range_succ, hockey m n]
    unfold bc
    rw [show n + 1 + (m + 1) = (n + m + 1) + 1 by ring, Nat.choose_succ_succ',
      show n + 1 + m = n + m + 1 by ring, show n + (m + 1) = n + m + 1 by ring]
    push_cast; ring

/-- `(m+1) · C(n+m+1, m+1) = (n+m+1) · C(n+m, m)`. -/
lemma bc_succ (m n : ℕ) : (m + 1 : ℝ) * bc (m + 1) n = (n + m + 1 : ℝ) * bc m n := by
  have := Nat.add_one_mul_choose_eq (n + m) m
  unfold bc
  rw [show n + (m + 1) = n + m + 1 by ring]
  have h : (((n + m + 1) * (n + m).choose m : ℕ) : ℝ) =
      (((n + m + 1).choose (m + 1) * (m + 1) : ℕ) : ℝ) := by rw [this]
  push_cast at h
  linarith

/-- Weighted Cesàro: `x n / C(n+m,m) → A` implies `(∑_{k≤n} x k) / C(n+m+1,m+1) → A`. -/
theorem weighted_cesaro {x : ℕ → ℝ} {A : ℝ} (m : ℕ)
    (hx : Tendsto (fun n => x n / bc m n) atTop (𝓝 A)) :
    Tendsto (fun n => (∑ k ∈ range (n + 1), x k) / bc (m + 1) n) atTop (𝓝 A) := by
  set f : ℕ → ℝ := fun k => x k - A * bc m k with hf
  have h1 : f =o[atTop] (bc m) := by
    refine Asymptotics.isLittleO_of_tendsto (fun k hk => absurd hk (bc_pos m k).ne') ?_
    have : (fun k => f k / bc m k) = fun k => x k / bc m k - A := by
      funext k; rw [hf]; field_simp [(bc_pos m k).ne']
    rw [this]
    simpa using hx.sub_const A
  have hsum : Tendsto (fun n => ∑ i ∈ range n, bc m i) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have : ∀ i ∈ range n, (1 : ℝ) ≤ bc m i := fun i _ => by
      unfold bc; exact_mod_cast Nat.choose_pos (by omega)
    have := Finset.card_nsmul_le_sum (range n) (bc m) 1 this
    simpa using this
  have h2 := (h1.sum_range (fun k => (bc_pos m k).le) hsum).tendsto_div_nhds_zero
  have h3 := ((tendsto_add_atTop_iff_nat 1).2 h2).add_const A
  rw [zero_add] at h3
  refine h3.congr (fun n => ?_)
  rw [hockey m n, hf, sum_sub_distrib, ← mul_sum, hockey m n]
  have := (bc_pos (m + 1) n).ne'
  field_simp
  ring

/-- Convolution with a convergent sequence. -/
theorem conv_tendsto {x y : ℕ → ℝ} {A B : ℝ} (m : ℕ)
    (hx : Tendsto (fun n => x n / bc m n) atTop (𝓝 A)) (hy : Tendsto y atTop (𝓝 B)) :
    Tendsto (fun n => (∑ k ∈ range (n + 1), x k * y (n - k)) / bc (m + 1) n) atTop
      (𝓝 (A * B)) := by
  set e : ℕ → ℝ := fun j => y j - B with he
  have hsplit : ∀ n, (∑ k ∈ range (n + 1), x k * y (n - k)) / bc (m + 1) n =
      B * ((∑ k ∈ range (n + 1), x k) / bc (m + 1) n) +
        (∑ k ∈ range (n + 1), x k * e (n - k)) / bc (m + 1) n := by
    intro n
    have : ∀ k, x k * y (n - k) = B * x k + x k * e (n - k) := fun k => by rw [he]; ring
    simp only [this, sum_add_distrib, ← mul_sum]
    ring
  simp only [hsplit]
  rw [show A * B = B * A + 0 by ring]
  refine ((weighted_cesaro m hx).const_mul B).add ?_
  -- the error term
  obtain ⟨M, hM⟩ := (hx.abs).bddAbove_range
  have hM' : ∀ k, |x k| ≤ M * bc m k := fun k => by
    have : |x k / bc m k| ≤ M := hM ⟨k, rfl⟩
    rw [abs_div, abs_of_pos (bc_pos m k), div_le_iff₀ (bc_pos m k)] at this
    exact this
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (x 0 / bc m 0)) (hM ⟨0, rfl⟩)
  have he0 : Tendsto (fun j => |e j|) atTop (𝓝 0) := by
    have := (hy.sub_const B).abs
    simpa [he] using this
  have hc := (tendsto_add_atTop_iff_nat 1).2 he0.cesaro
  have hc' := hc.const_mul (M * (m + 1))
  rw [mul_zero] at hc'
  refine squeeze_zero_norm (fun n => ?_) hc'
  have hb := bc_pos (m + 1) n
  have hbm := bc_pos m n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hb]
  have s1 : |∑ k ∈ range (n + 1), x k * e (n - k)| ≤
      M * bc m n * ∑ j ∈ range (n + 1), |e j| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hr := Finset.sum_range_reflect (fun j => |e j|) (n + 1)
    simp only [Nat.add_sub_cancel] at hr
    rw [← hr, mul_sum]
    refine sum_le_sum (fun k hk => ?_)
    rw [abs_mul]
    have := mem_range.1 hk
    exact mul_le_mul_of_nonneg_right ((hM' k).trans
      (mul_le_mul_of_nonneg_left (bc_mono m (by omega)) hM0)) (abs_nonneg _)
  have s2 := bc_succ m n
  have hS : 0 ≤ ∑ j ∈ range (n + 1), |e j| := sum_nonneg (fun _ _ => abs_nonneg _)
  push_cast
  rw [div_le_iff₀ hb]
  refine s1.trans ?_
  -- `M C(n+m,m) Σ ≤ M (m+1) Σ/(n+1) · C(n+m+1,m+1)`
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have key : bc m n * (n + 1) ≤ (m + 1) * bc (m + 1) n := by
    rw [s2]; nlinarith
  rw [show M * (m + 1) * ((↑n + 1)⁻¹ * ∑ j ∈ range (n + 1), |e j|) * bc (m + 1) n =
    M * ((m + 1) * bc (m + 1) n) * (∑ j ∈ range (n + 1), |e j|) / (n + 1) by field_simp]
  rw [le_div_iff₀ hn1]
  have := mul_le_mul_of_nonneg_left key hM0
  have := mul_le_mul_of_nonneg_right this hS
  nlinarith

/-! ### 3. Asymptotics of `[zⁿ] D_r^{−(m+1)}` -/

/-- `v r m n = [zⁿ] D_r^{−(m+1)} · ρⁿ`. -/
noncomputable def v (r m n : ℕ) : ℝ := (cm r m n : ℝ) * rho r ^ n

/-- Simple pole: `[zⁿ] (1/D_r) · ρⁿ → 1/K_r`. -/
theorem v_zero_tendsto (r : ℕ) : Tendsto (v r 0) atTop (𝓝 (1 / Kr r)) := by
  have hrec : ∀ n, v r 0 (n + r + 1) = rho r * v r 0 (n + r) + rho r ^ (r + 1) * v r 0 n := by
    intro n
    simp only [v, cm_zero, cZ_rec]
    push_cast; ring
  have h := tendsto_of_averaging (rho_pos r) (rho_lt_one r).le (pow_nonneg (rho_pos r).le _)
    (rho_eq r) hrec
  have hJ : Jinv r (v r 0) (rho r ^ (r + 1)) 0 = 1 := by
    unfold Jinv
    have e1 : ∀ i ∈ range r, v r 0 (0 + i) = rho r ^ i := fun i hi => by
      rw [v, cm_zero, zero_add, cZ_of_le r i (by simp at hi; omega)]; simp
    rw [sum_congr rfl e1, zero_add, v, cm_zero, cZ_of_le r r le_rfl]
    have g := mul_neg_geom_sum (rho r) r
    have hq : 1 - rho r = rho r ^ (r + 1) := by linarith [rho_eq r]
    rw [hq] at g
    push_cast
    linarith
  have hK : 1 + (r : ℝ) * rho r ^ (r + 1) = Kr r := by
    unfold Kr; have := rho_eq r; linear_combination (-1 : ℝ) * this
  rw [hJ, hK] at h
  exact h

lemma v_succ (r m n : ℕ) :
    v r (m + 1) n = ∑ k ∈ range (n + 1), v r m k * v r 0 (n - k) := by
  rw [v, cm_succ]
  push_cast
  rw [sum_mul]
  refine sum_congr rfl (fun k hk => ?_)
  have hk' : k + (n - k) = n := by have := mem_range.1 hk; omega
  rw [v, v, cm_zero]
  rw [show rho r ^ n = rho r ^ k * rho r ^ (n - k) by rw [← pow_add, hk']]
  ring

/-- `[zⁿ] D_r^{−(m+1)} · ρⁿ / C(n+m, m) → 1/K_r^{m+1}`. -/
theorem v_tendsto_bc (r : ℕ) : ∀ m, Tendsto (fun n => v r m n / bc m n) atTop
    (𝓝 (1 / Kr r ^ (m + 1)))
  | 0 => by
    have : (fun n => v r 0 n / bc 0 n) = v r 0 := by funext n; simp [bc]
    rw [this, zero_add, pow_one]; exact v_zero_tendsto r
  | m + 1 => by
    have h := conv_tendsto m (v_tendsto_bc r m) (v_zero_tendsto r)
    have hK := (Kr_pos r).ne'
    rw [show 1 / Kr r ^ (m + 1) * (1 / Kr r) = 1 / Kr r ^ (m + 1 + 1) by
      rw [pow_succ]; field_simp; ring] at h
    refine h.congr (fun n => ?_)
    rw [v_succ]

/-- `C(n+m, m) / n^m → 1/m!`. -/
theorem bc_div_pow_tendsto : ∀ m : ℕ, Tendsto (fun n : ℕ => bc m n / (n : ℝ) ^ m) atTop
    (𝓝 (1 / (m.factorial : ℝ)))
  | 0 => by simp [bc]
  | m + 1 => by
    have ih := bc_div_pow_tendsto m
    have h1 : Tendsto (fun n : ℕ => (1 + ((m : ℝ) + 1) / n) / (m + 1)) atTop
        (𝓝 ((1 + 0) / (m + 1))) :=
      ((tendsto_const_div_atTop_nhds_zero_nat ((m : ℝ) + 1)).const_add 1).div_const _
    have h := h1.mul ih
    rw [show (1 + 0) / ((m : ℝ) + 1) * (1 / (m.factorial : ℝ)) = 1 / ((m + 1).factorial : ℝ) by
      rw [Nat.factorial_succ]; push_cast; field_simp; simp] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have s := bc_succ m n
    have hm : (0 : ℝ) < m + 1 := by positivity
    rw [show bc (m + 1) n = ((n : ℝ) + m + 1) * bc m n / (m + 1) by
      field_simp; linarith]
    field_simp
    ring

/-- **Pole of order `m+1`**: `[zⁿ] D_r^{−(m+1)} · ρⁿ / n^m → 1/(m! K_r^{m+1})`. -/
theorem v_tendsto (r m : ℕ) : Tendsto (fun n : ℕ => v r m n / (n : ℝ) ^ m) atTop
    (𝓝 (1 / ((m.factorial : ℝ) * Kr r ^ (m + 1)))) := by
  have h := (v_tendsto_bc r m).mul (bc_div_pow_tendsto m)
  rw [show 1 / Kr r ^ (m + 1) * (1 / (m.factorial : ℝ)) =
    1 / ((m.factorial : ℝ) * Kr r ^ (m + 1)) by ring] at h
  refine h.congr (fun n => ?_)
  have := (bc_pos m n).ne'
  field_simp

/-! ### 4. The moments -/

lemma ratio_tendsto (i : ℕ) : Tendsto (fun n : ℕ => ((n - i : ℕ) : ℝ) / n) atTop (𝓝 1) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ)).const_sub 1
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (i + 1)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Nat.cast_sub (by omega)]
  field_simp

/-- Value of the numerator at `ρ`: `P(ρ) = (2m)! ρ^{(r+1)m−r}` since `D_r(ρ) = 0`. -/
lemma aeval_numerator {r m : ℕ} (P q : Polynomial ℤ)
    (hPq : P = Polynomial.C (((2 * m).factorial : ℕ) : ℤ) * Polynomial.X ^ ((r + 1) * m - r) +
        (1 - Polynomial.X - Polynomial.X ^ (r + 1)) * q) :
    Polynomial.aeval (rho r) P = ((2 * m).factorial : ℝ) * rho r ^ ((r + 1) * m - r) := by
  have h0 : 1 - rho r - rho r ^ (r + 1) = 0 := by linarith [rho_eq r]
  rw [hPq]
  simp [h0]

/-- **Main theorem.** For `r ≥ 1`, `m ≥ 1`:
`Tr(A_{n,r}^{2m}) · ρⁿ / n^m → (2m)! ρ^{(r+1)m−r} / (m! K_r^{m+1})`. -/
theorem tendsto_moment {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => (Mk (2 * m) r n : ℝ) * rho r ^ n / (n : ℝ) ^ m) atTop
      (𝓝 (((2 * m).factorial : ℝ) * rho r ^ ((r + 1) * m - r) /
        ((m.factorial : ℝ) * Kr r ^ (m + 1)))) := by
  obtain ⟨P, q, hdeg, hS, hPq⟩ := General.moment_residue hr hm
  set d := (2 * r + 1) * (m - 1) + 1
  set L := 1 / ((m.factorial : ℝ) * Kr r ^ (m + 1)) with hL
  have hterm : ∀ i ∈ range (d + 1), Tendsto (fun n : ℕ => (P.coeff i : ℝ) * rho r ^ i *
      (v r m (n - i) / ((n - i : ℕ) : ℝ) ^ m) * (((n - i : ℕ) : ℝ) / n) ^ m) atTop
      (𝓝 ((P.coeff i : ℝ) * rho r ^ i * L * 1 ^ m)) := fun i _ =>
    (((v_tendsto r m).comp (tendsto_sub_atTop_nat i)).const_mul _).mul
      ((ratio_tendsto i).pow m)
  have hsum := tendsto_finsetSum (range (d + 1)) hterm
  have hval : ∑ i ∈ range (d + 1), (P.coeff i : ℝ) * rho r ^ i * L * 1 ^ m =
      ((2 * m).factorial : ℝ) * rho r ^ ((r + 1) * m - r) / ((m.factorial : ℝ) * Kr r ^ (m + 1)) := by
    have ha := Polynomial.aeval_eq_sum_range' (show P.natDegree < d + 1 by omega) (rho r)
    rw [aeval_numerator P q hPq] at ha
    simp only [one_pow, mul_one, ← sum_mul, zsmul_eq_mul] at ha ⊢
    rw [← ha, hL]; ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (d + 1)] with n hn
  rw [Mk_eq_sum P hdeg hS (by omega), Int.cast_sum, sum_mul, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl (fun i hi => ?_)
  have hi' := mem_range.1 hi
  have hni : ((n - i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n - i ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [show rho r ^ n = rho r ^ i * rho r ^ (n - i) by rw [← pow_add]; congr 1; omega, v,
    div_pow]
  push_cast
  field_simp

/-- **Normalised moments.** `Tr(A_{n,r}^{2m}) / (a_{n,r} n^m) → ((2m)!/m!) (ρ^{r+1}/K_r)^m`. -/
theorem tendsto_moment_normalised {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => (Mk (2 * m) r n : ℝ) / ((a r n : ℝ) * (n : ℝ) ^ m)) atTop
      (𝓝 (((2 * m).factorial : ℝ) / (m.factorial : ℝ) * (rho r ^ (r + 1) / Kr r) ^ m)) := by
  have h := (tendsto_moment hr hm).div (tendsto_a_mul_rho_pow r)
    (by rw [Br_rho]; have := rho_pos r; have := Kr_pos r; positivity)
  have hρ := (rho_pos r).ne'
  have hK := (Kr_pos r).ne'
  have hc : ((2 * m).factorial : ℝ) * rho r ^ ((r + 1) * m - r) /
      ((m.factorial : ℝ) * Kr r ^ (m + 1)) / (Br r (rho r) / Kr r) =
      ((2 * m).factorial : ℝ) / (m.factorial : ℝ) * (rho r ^ (r + 1) / Kr r) ^ m := by
    rw [Br_rho]
    have e : rho r ^ ((r + 1) * m - r) * rho r ^ r = (rho r ^ (r + 1)) ^ m := by
      rw [← pow_add, ← pow_mul, Nat.sub_add_cancel (by nlinarith)]
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    rw [e, div_pow]
    field_simp
    ring
  rw [hc] at h
  refine h.congr (fun n => ?_)
  have hn : rho r ^ n ≠ 0 := pow_ne_zero _ hρ
  simp only [Pi.div_apply]
  rw [div_div, mul_comm ((n : ℝ) ^ m), mul_right_comm _ (rho r ^ n), mul_div_mul_right _ _ hn]

/-- The same limit as Gaussian moments: `((2m)!/(m! 2^m)) σ_r^{2m}` with `σ_r² = 2ρ^{r+1}/K_r`,
i.e. `(2m−1)!! σ_r^{2m}`. -/
theorem tendsto_moment_gaussian {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => (Mk (2 * m) r n : ℝ) / ((a r n : ℝ) * (n : ℝ) ^ m)) atTop
      (𝓝 (((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * 2 ^ m) * sigmaSq r ^ m)) := by
  have h := tendsto_moment_normalised hr hm
  have hK := (Kr_pos r).ne'
  convert h using 2
  unfold sigmaSq
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  rw [div_pow, div_pow, mul_pow]
  field_simp

/-- `(2m)!/(m! 2^m) = (2m−1)!!`. -/
lemma factorial_div_eq_doubleFactorial {m : ℕ} (hm : 1 ≤ m) :
    ((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * 2 ^ m) = (Nat.doubleFactorial (2 * m - 1) : ℝ) := by
  have h := Nat.factorial_eq_mul_doubleFactorial (2 * m - 1)
  rw [show 2 * m - 1 + 1 = 2 * m by omega, Nat.doubleFactorial_two_mul] at h
  rw [h]
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-! ### 5. Odd moments vanish (the constrained hypercube is bipartite) -/

/-- The sign `(−1)^{#ones}` of a word. -/
def sgn (w : List Bool) : ℤ := (-1) ^ w.count true

lemma sgn_flip {w : List Bool} {i : ℕ} (h : i < w.length) : sgn (flip w i) = -sgn w := by
  unfold sgn flip
  rw [List.count_set h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  cases hb : w[i]
  · simp [pow_succ]
  · have hpos : 0 < w.count true := List.count_pos_iff.2 (hb ▸ List.getElem_mem h)
    obtain ⟨c, hc⟩ : ∃ c, w.count true = c + 1 := ⟨w.count true - 1, by omega⟩
    simp [hc, pow_succ]

lemma sgn_sq (w : List Bool) : sgn w * sgn w = 1 := by
  unfold sgn; rw [← pow_add, ← two_mul, pow_mul]; simp

/-- **Odd moments vanish**: `Tr A_{n,r}^{2m+1} = 0` (all `r, n, m`). -/
theorem Mk_odd (r n m : ℕ) : Mk (2 * m + 1) r n = 0 := by
  classical
  set S : Matrix (V r n) (V r n) ℤ := Matrix.diagonal (fun u => sgn u.1) with hS
  set A := adjMat r n
  have hSS : S * S = 1 := by
    rw [hS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext u; exact sgn_sq u.1
  have hSAS : S * A * S = -A := by
    ext u v
    rw [hS, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
    simp only [A, adjMat, Matrix.of_apply]
    split_ifs with hadj
    · obtain ⟨i, hi, hv⟩ := hadj
      rw [hv, sgn_flip (mem_range.1 hi)]
      have := sgn_sq u.1
      linear_combination (-1 : ℤ) * this
    · simp
  have hpow : ∀ k, S * A ^ k * S = (S * A * S) ^ k := by
    intro k
    induction k with
    | zero => simpa using hSS
    | succ k ih =>
      rw [pow_succ, pow_succ, ← ih]
      calc S * (A ^ k * A) * S = S * A ^ k * (S * S) * A * S := by
            rw [hSS]; simp only [Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = S * A ^ k * S * (S * A * S) := by simp only [Matrix.mul_assoc]
  have ht : Matrix.trace (A ^ (2 * m + 1)) = -Matrix.trace (A ^ (2 * m + 1)) := by
    calc Matrix.trace (A ^ (2 * m + 1)) = Matrix.trace (S * A ^ (2 * m + 1) * S) := by
          rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hSS, Matrix.one_mul]
      _ = -Matrix.trace (A ^ (2 * m + 1)) := by
          rw [hpow, hSAS, Odd.neg_pow ⟨m, rfl⟩, Matrix.trace_neg]
  unfold Mk
  linarith

end APEX.Blockade.Asymptotics

