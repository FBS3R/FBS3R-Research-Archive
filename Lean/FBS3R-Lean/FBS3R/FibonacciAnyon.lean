/-
# Exact braid algebra of the Fibonacci anyon qubit

Source: *Exact Braid Algebra and Diamond-Norm Bounds for a Phenomenological Noisy Fibonacci
Anyon Qubit* (2026-11-09).  The paper takes
`F = [[u, v], [v, -u]]` with `u = φ⁻¹`, `v = √u`, `R = diag(e^{-4πi/5}, e^{3πi/5})`,
`B₁ = R`, `B₂ = F R F`, and claims `F² = 1` and the braid relation `B₁B₂B₁ = B₂B₁B₂`.

Machine-checked here:
* `F_sq` : `F² = 1` over any commutative ring as soon as `v⁴ + v² = 1` (i.e. `u² + u = 1`).
* `braid_defect` : a **closed form of the braid defect** for an arbitrary diagonal `R = diag(a,b)`:
  `R F R F R - F R F R F R F = (a-b)·Q(a,b) • [[1,-v],[-v,-1]]`, with
  `Q(a,b) = (2u-1)a² + (2-3u)ab + (2u-1)b²`.
* `braid_iff` : over a field, the braid relation holds **iff** `a = b` or `Q(a,b) = 0`
  (a characterisation not stated in the paper).
* `fibonacci_braid` : the paper's concrete phases satisfy it, so `B₁B₂B₁ = B₂B₁B₂` exactly.

Not formalised: the diamond-norm estimates (Mathlib has no diamond norm / CPTP channels).
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

namespace FBS3R.FibonacciAnyon

open Matrix

section General
variable {K : Type*} [CommRing K]

/-- The `F`-move written with `u = v²`. -/
def Fm (v : K) : Matrix (Fin 2) (Fin 2) K := !![v ^ 2, v; v, -v ^ 2]

/-- A diagonal `R`-move. -/
def Rm (a b : K) : Matrix (Fin 2) (Fin 2) K := !![a, 0; 0, b]

/-- The quadratic form controlling the braid relation. -/
def Q (v a b : K) : K := (2 * v ^ 2 - 1) * a ^ 2 + (2 - 3 * v ^ 2) * a * b + (2 * v ^ 2 - 1) * b ^ 2

theorem F_sq (v : K) (h : v ^ 4 + v ^ 2 = 1) : Fm v * Fm v = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Fm, Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination h | ring1

theorem braid_defect (v a b : K) (h : v ^ 4 + v ^ 2 = 1) :
    Rm a b * Fm v * Rm a b * Fm v * Rm a b
      - Fm v * Rm a b * Fm v * Rm a b * Fm v * Rm a b * Fm v
      = ((a - b) * Q v a b) • !![1, -v; -v, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Fm, Rm, Q]
  · linear_combination (-a^3*v^4 + a^3*v^2 - a^3 - 3*a^2*b*v^2 + 3*a^2*b + 2*a*b^2*v^2
      - 3*a*b^2 - b^3*v^2 + b^3) * h
  · linear_combination (-v*(a - b)*(a^2*v^2 - a^2 + 2*a*b + b^2*v^2 - b^2)) * h
  · linear_combination (-v*(a - b)*(a^2*v^2 - a^2 + 2*a*b + b^2*v^2 - b^2)) * h
  · linear_combination (-a^3*v^2 + a^3 + 2*a^2*b*v^2 - 3*a^2*b - 3*a*b^2*v^2 + 3*a*b^2
      - b^3*v^4 + b^3*v^2 - b^3) * h

theorem braid_iff {L : Type*} [Field L] (v a b : L) (h : v ^ 4 + v ^ 2 = 1) :
    Rm a b * Fm v * Rm a b * Fm v * Rm a b
      = Fm v * Rm a b * Fm v * Rm a b * Fm v * Rm a b * Fm v ↔ a = b ∨ Q v a b = 0 := by
  rw [← sub_eq_zero, braid_defect v a b h]
  constructor
  · intro hz
    have := congrFun (congrFun hz 0) 0
    simp at this
    rcases this with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr h1
  · rintro (h1 | h1) <;> simp [h1]

end General

open Complex Real

/-- `u = φ⁻¹ = (√5 - 1)/2`. -/
noncomputable def u : ℝ := (√5 - 1) / 2
/-- `v = √u`. -/
noncomputable def v : ℝ := √u

theorem u_eq_inv_gold : u = goldenRatio⁻¹ := by
  rw [inv_goldenRatio, goldenConj]; unfold u; ring

theorem u_pos : 0 < u := by
  unfold u
  have : (1:ℝ) < √5 := by
    rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem u_quad : u ^ 2 + u = 1 := by
  unfold u
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination h5 / 4

theorem v_sq : v ^ 2 = u := Real.sq_sqrt u_pos.le

theorem v_quartic : (v : ℂ) ^ 4 + (v : ℂ) ^ 2 = 1 := by
  have : v ^ 4 + v ^ 2 = 1 := by
    rw [show v ^ 4 = (v ^ 2) ^ 2 by ring, v_sq]; exact u_quad
  exact_mod_cast this

/-- `cos(3π/5) = -u/2`. -/
theorem cos_three_pi_div_five : Real.cos (3 * π / 5) = -u / 2 := by
  have h1 : 3 * π / 5 = π - 2 * (π / 5) := by ring
  rw [h1, Real.cos_pi_sub, Real.cos_two_mul, Real.cos_pi_div_five]
  unfold u
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (-1/8 : ℝ) * h5

/-- The paper's `R`-matrix phases. -/
noncomputable def a : ℂ := Complex.exp (-(4 * π / 5) * I)
noncomputable def b : ℂ := Complex.exp ((3 * π / 5) * I)

theorem a_eq_b_sq : a = b ^ 2 := by
  unfold a b
  rw [← Complex.exp_nat_mul]
  have : ((2:ℕ):ℂ) * ((3 * π / 5) * I) = (-(4 * π / 5) * I) + 2 * π * I := by push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem b_sq_add_one : b ^ 2 + 1 = -(u : ℂ) * b := by
  unfold b
  rw [Complex.exp_mul_I]
  set z : ℂ := (3 * π / 5 : ℂ)
  have hc : Complex.cos z = ((Real.cos (3 * π / 5) : ℝ) : ℂ) := by
    simp [z, Complex.ofReal_cos]
  have hpy := Complex.cos_sq_add_sin_sq z
  rw [cos_three_pi_div_five] at hc
  push_cast at hc
  linear_combination 2 * (Complex.cos z + Complex.sin z * I) * hc - hpy + Complex.sin z ^ 2 * I_sq

theorem Q_vanishes : Q (v : ℂ) a b = 0 := by
  have hv : (v : ℂ) ^ 2 = u := by exact_mod_cast v_sq
  have hu : (u : ℂ) ^ 2 + u = 1 := by exact_mod_cast u_quad
  rw [Q, a_eq_b_sq, hv]
  have hb := b_sq_add_one
  linear_combination b ^ 2 * (2 * (u:ℂ) - 1) * hb - 2 * b ^ 3 * hu

/-- **The braid relation of the paper holds exactly**: with `B₁ = R`, `B₂ = F R F`,
`B₁ B₂ B₁ = B₂ B₁ B₂`, where `F = [[u,v],[v,-u]]`, `u = φ⁻¹`, `v = √u`,
`R = diag(e^{-4πi/5}, e^{3πi/5})`. -/
theorem fibonacci_braid :
    let F : Matrix (Fin 2) (Fin 2) ℂ := !![(u:ℂ), v; v, -(u:ℂ)]
    let R : Matrix (Fin 2) (Fin 2) ℂ := !![a, 0; 0, b]
    let B₁ := R
    let B₂ := F * R * F
    B₁ * B₂ * B₁ = B₂ * B₁ * B₂ ∧ F * F = 1 := by
  intro F R B₁ B₂
  have hv : (u : ℂ) = (v : ℂ) ^ 2 := by exact_mod_cast v_sq.symm
  have hF : F = Fm (v : ℂ) := by simp only [F, Fm, hv]
  have hR : R = Rm a b := rfl
  refine ⟨?_, ?_⟩
  · have := (braid_iff (v : ℂ) a b v_quartic).mpr (Or.inr Q_vanishes)
    simp only [B₁, B₂, hF, hR, Matrix.mul_assoc] at this ⊢
    exact this
  · rw [hF]; exact F_sq _ v_quartic

end FBS3R.FibonacciAnyon
