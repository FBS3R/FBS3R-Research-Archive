import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.BigOperators.Field

/-!
# Moment–cumulant hierarchy and Prony recovery for finite mixtures of point masses

## Cumulants (any commutative ring `R`; generating functions over a field `K` of char. 0)
* `cumulant m`: `κ 0 = 0`, `κ (n+1) = m (n+1) - Σ_{j<n} C(n,j) κ (j+1) m (n-j)`
  (i.e. `κ_N = m_N - Σ_{k=1}^{N-1} C(N-1,k-1) κ_k m_{N-k}`).
* `moment_succ_eq`, `cumulant_unique`: with `m 0 = 1`, `m_{n+1} = Σ_{j≤n} C(n,j) κ_{j+1} m_{n-j}`,
  and `κ` is the unique sequence with `κ 0 = 0` satisfying this.
* `derivative_egf_moment`: `M' = K' · M` for `M = Σ m_n tⁿ/n!`, `K = Σ κ_n tⁿ/n!`;
  `egf_cumulant_unique`: `K` is the unique series with `K(0) = 0` and `M' = K' M`.
* `egf_moment_eq_exp_cumulant`: `M = exp(K)` as formal power series
  (`(PowerSeries.exp K).subst K`).
* `cumulant_bconv` (additivity): for `m^{X+Y}_n = Σ C(n,k) m^X_k m^Y_{n-k}`, `κ^{X+Y} = κ^X + κ^Y`.
* `cumulant_scale` (scaling, any comm. ring): `κ_n(cX) = cⁿ κ_n(X)`.

## Prony (any field `K`), `μ = Σ_{i<p} w_i δ_{x_i}`, `s_n = Σ w_i x_iⁿ` (`pmoment`)
* `det_vand`: Vandermonde determinant `Π_{i<j} (x_j - x_i)` (proved here, since
  `Mathlib.LinearAlgebra.Vandermonde` is not built in this environment; `vand` has the same
  convention as `Matrix.vandermonde`).
* `hankel_eq_vand`: `H_p = Vᵀ diag(w) V`; `det_hankel`: `det H_p = Π w_i · (Π_{i<j}(x_j-x_i))²`;
  `det_hankel_ne_zero` for distinct nodes and nonzero weights.
* `prony_recurrence`: `s_{n+p} + Σ_{k<p} c_k s_{n+k} = 0` for `q = Π(z - x_i) = z^p + Σ c_k z^k`;
  `hankel_mulVec_pronyCoeff`, `pronyCoeff_unique`: `c` is the unique solution of
  `H_p c = -(s_p,…,s_{2p-1})`. `roots_pronyPoly`: roots of `q` = node multiset.
* `prony_identifiable`: equal `s_0..s_{2p-1}` (distinct nodes, the first mixture with nonzero
  weights, the second with distinct nodes) give equal Prony polynomials, equal node multisets,
  and a permutation `σ` with `y = x ∘ σ`, `u = w ∘ σ`.
* `det_hankel_eq_zero_of_lt` (`det H_m = 0` for `m > p`), `det_hankel_succ_eq_zero`,
  `rank_hankel` (`rank H_m = p` for `m ≥ p`), `prony_order_unique` (`p` is determined).
-/

open Finset Matrix

namespace APEX.Spectral

section Vandermonde

variable {R : Type*} [CommRing R]

/-- Vandermonde matrix `vand v i j = v i ^ j` (same convention as `Matrix.vandermonde`). -/
def vand {n : ℕ} (v : Fin n → R) : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => v i ^ (j : ℕ)

theorem det_vand {n : ℕ} (v : Fin n → R) :
    det (vand v) = ∏ i : Fin n, ∏ j ∈ Ioi i, (v j - v i) := by
  unfold vand
  induction n with
  | zero => exact det_eq_one_of_card_eq_zero (Fintype.card_fin 0)
  | succ n ih =>
  calc
    det (of fun i j : Fin n.succ => v i ^ (j : ℕ)) =
        det (of fun i j : Fin n.succ =>
            Matrix.vecCons (v 0 ^ (j : ℕ)) (fun i => v (Fin.succ i) ^ (j : ℕ) - v 0 ^ (j : ℕ)) i) :=
      det_eq_of_forall_row_eq_smul_add_const (Matrix.vecCons 0 1) 0 (Fin.cons_zero _ _) ?_
    _ = det (of fun i j : Fin n =>
            Matrix.vecCons (v 0 ^ (j.succ : ℕ))
              (fun i : Fin n => v (Fin.succ i) ^ (j.succ : ℕ) - v 0 ^ (j.succ : ℕ))
              (Fin.succAbove 0 i)) := by
      simp_rw [det_succ_column_zero, Fin.sum_univ_succ, of_apply, Matrix.cons_val_zero, submatrix,
        of_apply, Matrix.cons_val_succ, Fin.val_zero, pow_zero, one_mul, sub_self,
        mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    _ = det (of fun i j : Fin n =>
          (v (Fin.succ i) - v 0) *
            ∑ k ∈ Finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ) :
          Matrix _ _ R) := by
      congr
      ext i j
      rw [Fin.succAbove_zero, Matrix.cons_val_succ, Fin.val_succ, mul_comm]
      exact (geom_sum₂_mul (v i.succ) (v 0) (j + 1 : ℕ)).symm
    _ = (∏ i ∈ Finset.univ, (v (Fin.succ i) - v 0)) *
          det (of fun i j : Fin n =>
            ∑ k ∈ Finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ)) :=
      (det_mul_column (fun i => v (Fin.succ i) - v 0) _)
    _ = (∏ i ∈ Finset.univ, (v (Fin.succ i) - v 0)) *
          det (of fun i j : Fin n => v (Fin.succ i) ^ (j : ℕ)) := congr_arg _ ?_
    _ = ∏ i : Fin n.succ, ∏ j ∈ Ioi i, (v j - v i) := by
      rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
      simp_rw [Fin.prod_Ioi_succ]
      have h := ih (v ∘ Fin.succ)
      unfold Function.comp at h
      rw [h]
  · intro i j
    simp_rw [of_apply]
    rw [Matrix.cons_val_zero]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    rw [Matrix.cons_val_succ, Matrix.cons_val_succ, Pi.one_apply]
    ring
  · cases n
    · rw [det_eq_one_of_card_eq_zero (Fintype.card_fin 0),
        det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
    apply det_eq_of_forall_col_eq_smul_add_pred fun _ => v 0
    · intro j
      simp
    · intro i j
      simp only [of_apply, Fin.val_succ, Fin.val_castSucc]
      rw [Finset.sum_range_succ, add_comm, tsub_self, pow_zero, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i' hi' => ?_
      rw [mul_left_comm (v 0), Nat.succ_sub, pow_succ']
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')

end Vandermonde

section Cumulants

variable {R : Type*} [CommRing R]

/-- Cumulants from moments: `κ 0 = 0` and
`κ (n+1) = m (n+1) - Σ_{j<n} C(n,j) κ (j+1) m (n-j)`, i.e.
`κ_N = m_N - Σ_{k=1}^{N-1} C(N-1,k-1) κ_k m_{N-k}`. -/
def cumulant (m : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => m (n + 1) - ∑ j : Fin n, (n.choose j : R) * cumulant m (j + 1) * m (n - j)
decreasing_by omega

@[simp] theorem cumulant_zero (m : ℕ → R) : cumulant m 0 = 0 := by
  rw [cumulant]

theorem cumulant_succ (m : ℕ → R) (n : ℕ) :
    cumulant m (n + 1) =
      m (n + 1) - ∑ j ∈ range n, (n.choose j : R) * cumulant m (j + 1) * m (n - j) := by
  rw [cumulant, Fin.sum_univ_eq_sum_range (fun j => (n.choose j : R) * cumulant m (j + 1) * m (n - j))]

/-- The recursion, read as the moment identity `m_{n+1} = Σ_{j ≤ n} C(n,j) κ_{j+1} m_{n-j}`
(coefficientwise form of `M' = K' M`). -/
theorem moment_succ_eq (m : ℕ → R) (hm0 : m 0 = 1) (n : ℕ) :
    m (n + 1) = ∑ j ∈ range (n + 1), (n.choose j : R) * cumulant m (j + 1) * m (n - j) := by
  rw [sum_range_succ, Nat.choose_self, Nat.sub_self, hm0, cumulant_succ]
  push_cast
  ring

/-- Uniqueness: any sequence `k` with `k 0 = 0` satisfying the moment identity is the cumulant
sequence. -/
theorem cumulant_unique (m k : ℕ → R) (hm0 : m 0 = 1) (hk0 : k 0 = 0)
    (hk : ∀ n, m (n + 1) = ∑ j ∈ range (n + 1), (n.choose j : R) * k (j + 1) * m (n - j)) :
    k = cumulant m := by
  funext N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | n
    · simp [hk0]
    · have h := hk n
      rw [sum_range_succ, Nat.choose_self, Nat.sub_self, hm0] at h
      rw [cumulant_succ]
      have hs : ∑ j ∈ range n, (n.choose j : R) * k (j + 1) * m (n - j) =
          ∑ j ∈ range n, (n.choose j : R) * cumulant m (j + 1) * m (n - j) := by
        refine sum_congr rfl fun j hj => ?_
        rw [ih (j + 1) (by simp at hj; omega)]
      rw [← hs, h]
      push_cast
      ring

/-- (c) Scaling: `κ_n(cX) = c^n κ_n(X)`, where `m_n(cX) = c^n m_n(X)`. -/
theorem cumulant_scale (m : ℕ → R) (hm0 : m 0 = 1) (c : R) (n : ℕ) :
    cumulant (fun n => c ^ n * m n) n = c ^ n * cumulant m n := by
  have h := cumulant_unique (fun n => c ^ n * m n) (fun n => c ^ n * cumulant m n)
    (by simp [hm0]) (by simp) (fun n => by
      rw [moment_succ_eq m hm0 n, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hj' : j ≤ n := by simp at hj; omega
      have : c ^ (n + 1) = c ^ (j + 1) * c ^ (n - j) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; ring)
  exact (congrFun h n).symm

/-- Binomial convolution of moment sequences: the moments of `X + Y` for independent `X, Y`. -/
def bconv (a b : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ range (n + 1), (n.choose k : R) * a k * b (n - k)

end Cumulants

section EGF

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

/-- Exponential generating function `Σ a_n t^n / n!`. -/
noncomputable def egf (a : ℕ → K) : K⟦X⟧ := PowerSeries.mk fun n => a n / (n.factorial : K)

omit [CharZero K] in
theorem coeff_egf (a : ℕ → K) (n : ℕ) : coeff n (egf a) = a n / (n.factorial : K) := by
  simp [egf]

omit [CharZero K] in
theorem constantCoeff_egf (a : ℕ → K) : constantCoeff (egf a) = a 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_egf]; simp

theorem egf_injective : Function.Injective (egf (K := K)) := by
  intro a b h
  funext n
  have := congrArg (coeff n) h
  rw [coeff_egf, coeff_egf] at this
  have hn : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp at this
  exact this

theorem derivative_egf (a : ℕ → K) : d⁄dX (egf a) = egf (fun n => a (n + 1)) := by
  ext n
  rw [coeff_derivative, coeff_egf, coeff_egf, Nat.factorial_succ]
  have hn : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn1 : ((n : K) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  push_cast
  field_simp

theorem egf_mul (a b : ℕ → K) : egf a * egf b = egf (bconv a b) := by
  ext n
  rw [coeff_mul, coeff_egf, bconv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; omega
  rw [coeff_egf, coeff_egf]
  have h : ((n.choose k : ℕ) : K) * (k.factorial : K) * ((n - k).factorial : K) =
      (n.factorial : K) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have h1 : (k.factorial : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h2 : ((n - k).factorial : K) ≠ 0 := by exact_mod_cast (n - k).factorial_ne_zero
  have h3 : ((n.choose k : ℕ) : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk').ne'
  rw [← h]
  field_simp

/-- (a) Derivative form of the moment–cumulant relation: `M' = K' · M` for the exponential
generating functions `M = Σ m_n t^n/n!`, `K = Σ κ_n t^n/n!`. -/
theorem derivative_egf_moment (m : ℕ → K) (hm0 : m 0 = 1) :
    d⁄dX (egf m) = d⁄dX (egf (cumulant m)) * egf m := by
  rw [derivative_egf, derivative_egf, egf_mul]
  congr 1
  funext n
  rw [moment_succ_eq m hm0 n, bconv]

/-- Uniqueness in (a): the cumulant series is the unique `L` with `L(0) = 0` and `M' = L' M`. -/
theorem egf_cumulant_unique (m : ℕ → K) (hm0 : m 0 = 1) (L : K⟦X⟧)
    (hL0 : constantCoeff L = 0) (hL : d⁄dX (egf m) = d⁄dX L * egf m) :
    L = egf (cumulant m) := by
  have hM : constantCoeff (egf m) ≠ 0 := by rw [constantCoeff_egf, hm0]; exact one_ne_zero
  have hd : d⁄dX L = d⁄dX (egf (cumulant m)) := by
    have h := hL.symm.trans (derivative_egf_moment m hm0)
    have := congrArg (· * (egf m)⁻¹) h
    simpa only [mul_assoc, PowerSeries.mul_inv_cancel _ hM, mul_one] using this
  have : HasUniqueDiv K := .of_module_rat K
  exact derivative.ext hd (by rw [hL0, constantCoeff_egf, cumulant_zero])

/-- (a) The formal exponential relation `Σ m_n t^n/n! = exp(Σ κ_n t^n/n!)`, with `exp(K)` the
formal substitution of `K` (constant term `0`) into `exp`. -/
theorem egf_moment_eq_exp_cumulant (m : ℕ → K) (hm0 : m 0 = 1) :
    egf m = (PowerSeries.exp K).subst (egf (cumulant m)) := by
  have : HasUniqueDiv K := .of_module_rat K
  set L := egf (cumulant m)
  have hL0 : constantCoeff L = 0 := by rw [constantCoeff_egf, cumulant_zero]
  have hS : HasSubst L := HasSubst.of_constantCoeff_zero' hL0
  set E := (PowerSeries.exp K).subst L
  have hE0 : constantCoeff E = 1 := by
    have := constantCoeff_subst_of_constantCoeff_zero (S := K) hL0 (PowerSeries.exp K)
    rw [constantCoeff_exp, map_one] at this
    exact this
  have hEd : d⁄dX E = E * d⁄dX L := by
    rw [derivative_subst hS, derivative_exp]
  have hE : constantCoeff E ≠ 0 := by rw [hE0]; exact one_ne_zero
  have hMd := derivative_egf_moment m hm0
  have h1 : d⁄dX (egf m * E⁻¹) = 0 := by
    rw [Derivation.leibniz, derivative_inv', hEd, hMd, smul_eq_mul, smul_eq_mul]
    have : E⁻¹ * E = 1 := PowerSeries.inv_mul_cancel _ hE
    linear_combination (-(egf m) * E⁻¹ * d⁄dX L) * this
  have h2 : egf m * E⁻¹ = 1 := by
    refine derivative.ext (h1.trans derivative_one.symm) ?_
    rw [map_mul, constantCoeff_inv, hE0, constantCoeff_egf, hm0]; simp
  calc egf m = egf m * E⁻¹ * E := by rw [mul_assoc, PowerSeries.inv_mul_cancel _ hE, mul_one]
    _ = E := by rw [h2, one_mul]

/-- (b) Additivity of cumulants under binomial convolution of moment sequences
(moments of a sum of independent variables): `κ^{X+Y} = κ^X + κ^Y`. -/
theorem cumulant_bconv (a b : ℕ → K) (ha : a 0 = 1) (hb : b 0 = 1) :
    cumulant (bconv a b) = cumulant a + cumulant b := by
  have hab : bconv a b 0 = 1 := by simp [bconv, ha, hb]
  apply egf_injective
  symm
  apply egf_cumulant_unique _ hab
  · rw [constantCoeff_egf]; simp
  · have e : egf (cumulant a + cumulant b) = egf (cumulant a) + egf (cumulant b) := by
      ext n; simp [coeff_egf, add_div]
    rw [e, ← egf_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_egf_moment a ha,
      derivative_egf_moment b hb, map_add]
    ring

end EGF

section Prony

open Polynomial

variable {K : Type*} [Field K] {p : ℕ}

/-- Moments `s_n = Σ_i w_i x_i^n` of the mixture `Σ_i w_i δ_{x_i}`. -/
def pmoment (w x : Fin p → K) (n : ℕ) : K := ∑ i, w i * x i ^ n

/-- Hankel matrix `(s_{i+j})_{0 ≤ i,j < m}`. -/
def hankel (s : ℕ → K) (m : ℕ) : Matrix (Fin m) (Fin m) K := Matrix.of fun i j => s (i + j)

/-- (2a) `H_p = Vᵀ D V` with `V` the Vandermonde matrix and `D = diag w`. -/
theorem hankel_eq_vand (w x : Fin p → K) :
    hankel (pmoment w x) p = (vand x)ᵀ * Matrix.diagonal w * vand x := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [hankel, pmoment, vand, Matrix.of_apply, Matrix.mul_diagonal,
    Matrix.transpose_apply, pow_add]
  refine sum_congr rfl fun k _ => ?_
  ring

/-- (2a) `det H_p = Π w_i · (Π_{i<j} (x_j - x_i))²`. -/
theorem det_hankel (w x : Fin p → K) :
    (hankel (pmoment w x) p).det =
      (∏ i, w i) * (∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)) ^ 2 := by
  rw [hankel_eq_vand, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    det_vand]
  ring

theorem det_vand_ne_zero {x : Fin p → K} (hx : Function.Injective x) : (vand x).det ≠ 0 := by
  rw [det_vand]
  refine prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun j hj => ?_
  exact sub_ne_zero.mpr fun h => (mem_Ioi.mp hj).ne' (hx h)

/-- (2a) Distinct nodes and nonzero weights give `det H_p ≠ 0`. -/
theorem det_hankel_ne_zero {w x : Fin p → K} (hx : Function.Injective x) (hw : ∀ i, w i ≠ 0) :
    (hankel (pmoment w x) p).det ≠ 0 := by
  rw [hankel_eq_vand, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  have := det_vand_ne_zero hx
  exact mul_ne_zero (mul_ne_zero this (prod_ne_zero_iff.mpr fun i _ => hw i)) this

/-- The Prony polynomial `q(z) = Π_i (z - x_i)`. -/
noncomputable def pronyPoly (x : Fin p → K) : K[X] := ∏ i, (X - C (x i))

theorem pronyPoly_monic (x : Fin p → K) : (pronyPoly x).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)

theorem pronyPoly_natDegree (x : Fin p → K) : (pronyPoly x).natDegree = p := by
  rw [pronyPoly, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)]
  simp

theorem pronyPoly_coeff_p (x : Fin p → K) : (pronyPoly x).coeff p = 1 := by
  have h := (pronyPoly_monic x).leadingCoeff
  rwa [leadingCoeff, pronyPoly_natDegree] at h

theorem eval_pronyPoly (x : Fin p → K) (z : K) : (pronyPoly x).eval z = ∏ i, (z - x i) := by
  simp [pronyPoly, eval_prod]

/-- The roots of the Prony polynomial are exactly the nodes (as a multiset). -/
theorem roots_pronyPoly (x : Fin p → K) : (pronyPoly x).roots = Multiset.map x univ.val := by
  have : pronyPoly x = ((Multiset.map x univ.val).map fun a => X - C a).prod := by
    rw [pronyPoly, prod_eq_multiset_prod, Multiset.map_map]; rfl
  rw [this, roots_multiset_prod_X_sub_C]

/-- Prony coefficients `c_k`, `k < p`: `q(z) = z^p + Σ_{k<p} c_k z^k`. -/
noncomputable def pronyCoeff (x : Fin p → K) : Fin p → K := fun k => (pronyPoly x).coeff k

/-- Full recurrence `Σ_{k ≤ p} q_k s_{n+k} = 0`, valid for any weights. -/
theorem prony_recurrence_full (w x : Fin p → K) (n : ℕ) :
    ∑ k ∈ range (p + 1), (pronyPoly x).coeff k * pmoment w x (n + k) = 0 := by
  simp only [pmoment, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun i _ => ?_
  have h := eval_eq_sum_range' (p := pronyPoly x) (n := p + 1)
    (by rw [pronyPoly_natDegree]; omega) (x i)
  have h0 : (pronyPoly x).eval (x i) = 0 := by
    rw [eval_pronyPoly]; exact prod_eq_zero (mem_univ i) (sub_self _)
  rw [h0] at h
  calc ∑ k ∈ range (p + 1), (pronyPoly x).coeff k * (w i * x i ^ (n + k))
      = w i * x i ^ n * ∑ k ∈ range (p + 1), (pronyPoly x).coeff k * x i ^ k := by
        rw [mul_sum]; refine sum_congr rfl fun k _ => ?_; rw [pow_add]; ring
    _ = 0 := by rw [← h, mul_zero]

/-- (2b) Prony's linear recurrence `s_{n+p} + Σ_{k<p} c_k s_{n+k} = 0` for all `n`. -/
theorem prony_recurrence (w x : Fin p → K) (n : ℕ) :
    pmoment w x (n + p) + ∑ k : Fin p, pronyCoeff x k * pmoment w x (n + k) = 0 := by
  have h := prony_recurrence_full w x n
  rw [sum_range_succ, pronyPoly_coeff_p x, one_mul, add_comm] at h
  simp only [pronyCoeff]
  rw [Fin.sum_univ_eq_sum_range (fun k => (pronyPoly x).coeff k * pmoment w x (n + k)) p]
  exact h

/-- (2b) The Prony coefficients solve the Hankel system `H_p c = -(s_p, …, s_{2p-1})`. -/
theorem hankel_mulVec_pronyCoeff (w x : Fin p → K) :
    hankel (pmoment w x) p *ᵥ pronyCoeff x = fun i : Fin p => -pmoment w x ((i : ℕ) + p) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, hankel, Matrix.of_apply]
  have h := prony_recurrence w x i
  have h2 : ∑ j : Fin p, pmoment w x (i + j) * pronyCoeff x j =
      ∑ j : Fin p, pronyCoeff x j * pmoment w x (i + j) :=
    sum_congr rfl fun _ _ => mul_comm _ _
  linear_combination h2 + h

/-- (2b) Uniqueness: for distinct nodes and nonzero weights, the Prony coefficients are the
unique solution of `H_p c = -(s_p, …, s_{2p-1})`. -/
theorem pronyCoeff_unique {w x : Fin p → K} (hx : Function.Injective x) (hw : ∀ i, w i ≠ 0)
    (c : Fin p → K) (hc : hankel (pmoment w x) p *ᵥ c = fun i : Fin p => -pmoment w x ((i : ℕ) + p)) :
    c = pronyCoeff x := by
  have h : hankel (pmoment w x) p *ᵥ (c - pronyCoeff x) = 0 := by
    rw [Matrix.mulVec_sub, hc, hankel_mulVec_pronyCoeff, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero (det_hankel_ne_zero hx hw) h)

/-- (2c) Equal moments `s_0, …, s_{2p-1}` force equal Prony polynomials. -/
theorem pronyPoly_eq_of_moments {w x u y : Fin p → K} (hx : Function.Injective x)
    (hw : ∀ i, w i ≠ 0) (hs : ∀ n < 2 * p, pmoment w x n = pmoment u y n) :
    pronyPoly x = pronyPoly y := by
  have hH : hankel (pmoment u y) p = hankel (pmoment w x) p := by
    ext i j
    simp only [hankel, Matrix.of_apply]
    exact (hs _ (by omega)).symm
  have hc : pronyCoeff y = pronyCoeff x := by
    refine pronyCoeff_unique hx hw _ ?_
    rw [← hH, hankel_mulVec_pronyCoeff]
    funext i
    rw [hs _ (by omega)]
  ext n
  rcases lt_trichotomy n p with h | rfl | h
  · exact (congrFun hc ⟨n, h⟩).symm
  · rw [pronyPoly_coeff_p, pronyPoly_coeff_p]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [pronyPoly_natDegree]; exact h),
      coeff_eq_zero_of_natDegree_lt (by rw [pronyPoly_natDegree]; exact h)]

/-- (2c) Identifiability of finite mixtures of point masses from `s_0, …, s_{2p-1}`:
the Prony polynomials agree, the node multisets agree (they are the roots of the Prony
polynomial), and there is a relabelling `σ` with `y = x ∘ σ` and `u = w ∘ σ`. -/
theorem prony_identifiable {w x u y : Fin p → K} (hx : Function.Injective x)
    (hy : Function.Injective y) (hw : ∀ i, w i ≠ 0)
    (hs : ∀ n < 2 * p, pmoment w x n = pmoment u y n) :
    pronyPoly x = pronyPoly y ∧ Multiset.map x univ.val = Multiset.map y univ.val ∧
      ∃ σ : Equiv.Perm (Fin p), ∀ i, y i = x (σ i) ∧ u i = w (σ i) := by
  have hq := pronyPoly_eq_of_moments hx hw hs
  refine ⟨hq, by rw [← roots_pronyPoly, ← roots_pronyPoly, hq], ?_⟩
  have hex : ∀ j, ∃ i, y j = x i := by
    intro j
    have h0 : (pronyPoly x).eval (y j) = 0 := by
      rw [hq, eval_pronyPoly]; exact prod_eq_zero (mem_univ j) (sub_self _)
    rw [eval_pronyPoly, prod_eq_zero_iff] at h0
    obtain ⟨i, _, hi⟩ := h0
    exact ⟨i, sub_eq_zero.mp hi⟩
  choose f hf using hex
  have hfinj : Function.Injective f := fun a b hab => hy (by rw [hf a, hf b, hab])
  set σ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hσ : ∀ j, y j = x (σ j) := hf
  refine ⟨σ, fun j => ⟨hσ j, ?_⟩⟩
  -- weights via the invertible (transposed) Vandermonde system
  set d : Fin p → K := fun i => w i - u (σ.symm i)
  have hd : (vand x)ᵀ *ᵥ d = 0 := by
    funext n
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, vand, Matrix.of_apply,
      Pi.zero_apply, d, mul_sub, sum_sub_distrib]
    have h1 := hs n (by omega)
    simp only [pmoment] at h1
    have h2 : ∑ j, u j * y j ^ (n : ℕ) = ∑ i, u (σ.symm i) * x i ^ (n : ℕ) := by
      rw [← Equiv.sum_comp σ (fun i => u (σ.symm i) * x i ^ (n : ℕ))]
      refine sum_congr rfl fun j _ => ?_
      rw [Equiv.symm_apply_apply, hσ j]
    have h3 : ∑ i, x i ^ (n : ℕ) * w i = ∑ i, w i * x i ^ (n : ℕ) :=
      sum_congr rfl fun _ _ => mul_comm _ _
    have h4 : ∑ i, x i ^ (n : ℕ) * u (σ.symm i) = ∑ i, u (σ.symm i) * x i ^ (n : ℕ) :=
      sum_congr rfl fun _ _ => mul_comm _ _
    rw [h3, h4, h1, h2, sub_self]
  have hdet : ((vand x)ᵀ).det ≠ 0 := by rw [Matrix.det_transpose]; exact det_vand_ne_zero hx
  have h0 := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hd) (σ j)
  simp only [d, Equiv.symm_apply_apply, Pi.zero_apply] at h0
  exact (sub_eq_zero.mp h0).symm

/-- (2d) For any weights, `det H_m = 0` for every `m > p`: the vector of Prony coefficients
`(q_0, …, q_p, 0, …)` is a nonzero kernel vector. -/
theorem det_hankel_eq_zero_of_lt (w x : Fin p → K) {m : ℕ} (hm : p < m) :
    (hankel (pmoment w x) m).det = 0 := by
  set v : Fin m → K := fun j => (pronyPoly x).coeff j
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h ⟨p, hm⟩
    simp only [v, Pi.zero_apply, pronyPoly_coeff_p] at this
    exact one_ne_zero this
  have hv : hankel (pmoment w x) m *ᵥ v = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, hankel, Matrix.of_apply, v, Pi.zero_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j => pmoment w x (i + j) * (pronyPoly x).coeff j) m]
    have hsub : range (p + 1) ⊆ range m := range_subset_range.mpr (by omega)
    rw [← sum_subset hsub (fun j _ hj => by
      rw [coeff_eq_zero_of_natDegree_lt (by rw [pronyPoly_natDegree]; simp at hj; omega),
        mul_zero])]
    rw [← prony_recurrence_full w x i]
    exact sum_congr rfl fun _ _ => mul_comm _ _
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hv⟩

/-- (2d) `H_{p+1}` is singular. -/
theorem det_hankel_succ_eq_zero (w x : Fin p → K) : (hankel (pmoment w x) (p + 1)).det = 0 :=
  det_hankel_eq_zero_of_lt w x (Nat.lt_succ_self p)

/-- (2d) Rank: for distinct nodes and nonzero weights, `rank H_m = p` for every `m ≥ p`, so the
number of components is read off as the (stable) rank of the Hankel matrices. -/
theorem rank_hankel {w x : Fin p → K} (hx : Function.Injective x) (hw : ∀ i, w i ≠ 0)
    {m : ℕ} (hm : p ≤ m) : (hankel (pmoment w x) m).rank = p := by
  apply le_antisymm
  · -- `H_m = A (D Aᵀ)` with `A : m × p`, `A i k = x_k ^ i`
    set A : Matrix (Fin m) (Fin p) K := Matrix.of fun i k => x k ^ (i : ℕ)
    have hfac : hankel (pmoment w x) m = A * (Matrix.diagonal w * Aᵀ) := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [hankel, pmoment, A, Matrix.of_apply, Matrix.diagonal_mul, Matrix.transpose_apply,
        pow_add]
      refine sum_congr rfl fun k _ => ?_
      ring
    rw [hfac]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width A)
  · have hsub : (hankel (pmoment w x) m).submatrix (Fin.castLE hm) (Fin.castLE hm) =
        hankel (pmoment w x) p := by
      ext i j
      simp [hankel]
    have h := Matrix.rank_submatrix_le (hankel (pmoment w x) m) (Fin.castLE hm) (Fin.castLE hm)
    rw [hsub, Matrix.rank_of_det_ne_zero (det_hankel_ne_zero hx hw), Fintype.card_fin] at h
    exact h

/-- (2d) The number of components is determined by the moments: two mixtures with distinct
nodes and nonzero weights, `p` resp. `q` components, and equal moments `s_n` for `n < 2 max(p,q)`
have `p = q`. -/
theorem prony_order_unique {q : ℕ} {w x : Fin p → K} {u y : Fin q → K}
    (hx : Function.Injective x) (hw : ∀ i, w i ≠ 0) (hy : Function.Injective y)
    (hu : ∀ i, u i ≠ 0) (hs : ∀ n < 2 * max p q, pmoment w x n = pmoment u y n) : p = q := by
  have hH : hankel (pmoment w x) (max p q) = hankel (pmoment u y) (max p q) := by
    ext i j
    simp only [hankel, Matrix.of_apply]
    exact hs _ (by omega)
  have h1 := rank_hankel hx hw (le_max_left p q)
  have h2 := rank_hankel hy hu (le_max_right p q)
  rw [hH] at h1
  exact h1.symm.trans h2

end Prony

end APEX.Spectral

