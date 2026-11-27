/-
# Positive spectral measures: Hankel positivity, log-convexity, variance, selection

One finite-sum layer behind several archive papers:
* *Geometric Reduction, Killing Response … Spectral Tomography for Navier–Stokes on S³*
  (2026-09-22): moments `m_n = Σ_k E_k κ_k^n` of the energy spectrum — Hankel positivity,
  log-convexity `m_n² ≤ m_{n-1}m_{n+1}`, spectral-variance identity, monotone effective Stokes
  frequency, sharp chiral bound `|Ξ| ≤ 2/3`, exact viscous spectral selection.
* *Finite Dilation Operator Algebra* (2026-08-09/10): positive valuation mixtures
  `ε = Σ C_s A^s` — Hankel positivity of `[D^{i+j} ε]` and the Bhatia–Davis envelope.

Everything is proved for arbitrary finite index sets and nonnegative weights.  The
identification of these weights with Navier–Stokes shell energies or valuation coefficients
is the papers' input and is not formalised.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

namespace FBS3R.Moments

open Finset Real

variable {ι : Type*} (s : Finset ι) (E κ : ι → ℝ)

/-- Spectral moments of a positive measure. -/
def m (n : ℕ) : ℝ := ∑ k ∈ s, E k * κ k ^ n

/-- **Hankel positivity**: `Σ_{i,j} x_i x_j m_{i+j} = Σ_k E_k (Σ_i x_i κ_k^i)² ≥ 0`. -/
theorem hankel_psd (hE : ∀ k ∈ s, 0 ≤ E k) (N : ℕ) (x : Fin (N + 1) → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * m s E κ (i + j) := by
  have h : ∑ i, ∑ j, x i * x j * m s E κ (i + j)
      = ∑ k ∈ s, E k * (∑ i, x i * κ k ^ (i : ℕ)) ^ 2 := by
    simp only [m, sq, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add]; ring
  rw [h]
  exact Finset.sum_nonneg fun k hk => mul_nonneg (hE k hk) (sq_nonneg _)

/-- **Log-convexity** of the moments (`κ ≥ 0`): `m_{n+1}² ≤ m_n m_{n+2}`. -/
theorem log_convex (hE : ∀ k ∈ s, 0 ≤ E k) (hκ : ∀ k ∈ s, 0 ≤ κ k) (n : ℕ) :
    m s E κ (n + 1) ^ 2 ≤ m s E κ n * m s E κ (n + 2) := by
  unfold m
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro k hk; exact mul_nonneg (hE k hk) (pow_nonneg (hκ k hk) _)
  · intro k hk; exact mul_nonneg (hE k hk) (pow_nonneg (hκ k hk) _)
  · intro k _; apply le_of_eq; ring

/-- **Spectral-variance identity**: `m₀m₂ − m₁² = ½ Σ_{k,l} E_k E_l (κ_k − κ_l)²`. -/
theorem variance_identity :
    m s E κ 0 * m s E κ 2 - m s E κ 1 ^ 2
      = (1 / 2) * ∑ k ∈ s, ∑ l ∈ s, E k * E l * (κ k - κ l) ^ 2 := by
  have e : ∀ k l, E k * E l * (κ k - κ l) ^ 2
      = (E k * κ k ^ 2) * E l + E k * (E l * κ l ^ 2) - 2 * ((E k * κ k) * (E l * κ l)) := by
    intro k l; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, m, pow_zero, mul_one, pow_one]
  ring

/-- **Monotone effective frequency** `Ω_n = m_{n+1}/m_n`. -/
theorem frequency_monotone (hE : ∀ k ∈ s, 0 ≤ E k) (hκ : ∀ k ∈ s, 0 ≤ κ k) (n : ℕ)
    (h0 : 0 < m s E κ n) (h1 : 0 < m s E κ (n + 1)) :
    m s E κ (n + 1) / m s E κ n ≤ m s E κ (n + 2) / m s E κ (n + 1) := by
  rw [div_le_div_iff₀ h0 h1]
  nlinarith [log_convex s E κ hE hκ n]

/-- **Bhatia–Davis envelope**: probability weights on `[a,b]` have
`Var ≤ (b − μ)(μ − a)`. -/
theorem bhatia_davis (p x : ι → ℝ) (a b : ℝ) (hp : ∀ k ∈ s, 0 ≤ p k) (h1 : ∑ k ∈ s, p k = 1)
    (hx : ∀ k ∈ s, a ≤ x k ∧ x k ≤ b) :
    let μ := ∑ k ∈ s, p k * x k
    (∑ k ∈ s, p k * x k ^ 2) - μ ^ 2 ≤ (b - μ) * (μ - a) := by
  intro μ
  have hpos : 0 ≤ ∑ k ∈ s, p k * ((b - x k) * (x k - a)) :=
    Finset.sum_nonneg fun k hk =>
      mul_nonneg (hp k hk) (mul_nonneg (by linarith [(hx k hk).2]) (by linarith [(hx k hk).1]))
  have e : ∑ k ∈ s, p k * ((b - x k) * (x k - a))
      = (a + b) * μ - a * b * (∑ k ∈ s, p k) - ∑ k ∈ s, p k * x k ^ 2 := by
    simp only [μ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [e, h1] at hpos
  nlinarith

/-- Pure-shell chirality `ξ = 2σ/(k+2)` obeys `|ξ| ≤ 2/3` for `k ≥ 1`, `σ = ±1`. -/
theorem shell_chirality_bound (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    |2 * σ / ((k : ℝ) + 2)| ≤ 2 / 3 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < k + 2 := by linarith
  rw [abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by norm_num)]
  rcases hσ with rfl | rfl <;> norm_num <;> linarith

/-- **Sharp universal chiral bound** (2026-09-22): with shell dissipations
`D_τ = (c/2)(1 − 2τσ/(k+2))`, the global chirality `Ξ = (ΣD₋ − ΣD₊)/(ΣD₋ + ΣD₊)` satisfies
`|Ξ| ≤ 2/3` for every non-Killing state (`k ≥ 1`). -/
theorem chiral_bound (c : ι → ℝ) (k : ι → ℕ) (σ : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hk : ∀ i ∈ s, 1 ≤ k i) (hσ : ∀ i ∈ s, σ i = 1 ∨ σ i = -1) (hpos : 0 < ∑ i ∈ s, c i) :
    let Dm := fun i => c i / 2 * (1 + 2 * σ i / ((k i : ℝ) + 2))
    let Dp := fun i => c i / 2 * (1 - 2 * σ i / ((k i : ℝ) + 2))
    |(∑ i ∈ s, Dm i - ∑ i ∈ s, Dp i) / (∑ i ∈ s, Dm i + ∑ i ∈ s, Dp i)| ≤ 2 / 3 := by
  intro Dm Dp
  have hsum : ∑ i ∈ s, Dm i + ∑ i ∈ s, Dp i = ∑ i ∈ s, c i := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; simp only [Dm, Dp]; ring
  have hdiff : ∑ i ∈ s, Dm i - ∑ i ∈ s, Dp i = ∑ i ∈ s, c i * (2 * σ i / ((k i : ℝ) + 2)) := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; simp only [Dm, Dp]; ring
  rw [hsum, hdiff, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |∑ i ∈ s, c i * (2 * σ i / ((k i : ℝ) + 2))|
      ≤ ∑ i ∈ s, |c i * (2 * σ i / ((k i : ℝ) + 2))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, c i * (2 / 3) := by
        apply Finset.sum_le_sum; intro i hi
        rw [abs_mul, abs_of_nonneg (hc i hi)]
        exact mul_le_mul_of_nonneg_left (shell_chirality_bound (k i) (hk i hi) (σ i) (hσ i hi))
          (hc i hi)
    _ = 2 / 3 * ∑ i ∈ s, c i := by rw [← Finset.sum_mul]; ring

/-- The constant `2/3` is attained by a single `k = 1` shell. -/
theorem chiral_bound_attained : |2 * (1 : ℝ) / (((1 : ℕ) : ℝ) + 2)| = 2 / 3 := by norm_num

/-- **Exact viscous spectral selection** (2026-09-22): if the lowest active level carries
energy `A₀ > 0` decaying at rate `λ`, and every other level decays at rate `≥ λ + Δ`, then the
energy fraction outside the lowest level obeys
`1 − P(t) ≤ ((1 − P(0))/P(0)) e^{−Δ t}` for `t ≥ 0`. -/
theorem viscous_selection (B₀ : ι → ℝ) (rate : ι → ℝ) (A₀ lam Δ t : ℝ) (hA : 0 < A₀)
    (hB : ∀ i ∈ s, 0 ≤ B₀ i) (hrate : ∀ i ∈ s, lam + Δ ≤ rate i) (ht : 0 ≤ t) :
    let A := A₀ * exp (-lam * t)
    let B := ∑ i ∈ s, B₀ i * exp (-rate i * t)
    let P0 := A₀ / (A₀ + ∑ i ∈ s, B₀ i)
    1 - A / (A + B) ≤ (1 - P0) / P0 * exp (-Δ * t) := by
  intro A B P0
  have hApos : 0 < A := mul_pos hA (exp_pos _)
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun i hi => mul_nonneg (hB i hi) (exp_pos _).le
  set B0 := ∑ i ∈ s, B₀ i
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg hB
  have hBle : B ≤ B0 * exp (-(lam + Δ) * t) := by
    simp only [B, B0, Finset.sum_mul]
    apply Finset.sum_le_sum; intro i hi
    apply mul_le_mul_of_nonneg_left _ (hB i hi)
    apply exp_le_exp.mpr; nlinarith [hrate i hi]
  have hS : A₀ + ∑ i ∈ s, B₀ i ≠ 0 := by
    have : 0 ≤ ∑ i ∈ s, B₀ i := Finset.sum_nonneg hB
    linarith
  have hP : (1 - P0) / P0 = B0 / A₀ := by
    simp only [P0, B0]; field_simp; ring
  rw [hP]
  have h1 : 1 - A / (A + B) = B / (A + B) := by field_simp; ring
  rw [h1]
  calc B / (A + B) ≤ B / A := div_le_div_of_nonneg_left hBnn hApos (by linarith)
    _ ≤ B0 * exp (-(lam + Δ) * t) / A := by gcongr
    _ = B0 / A₀ * exp (-Δ * t) := by
        simp only [A]
        rw [show -(lam + Δ) * t = -lam * t + -Δ * t by ring, exp_add]
        field_simp

end FBS3R.Moments
