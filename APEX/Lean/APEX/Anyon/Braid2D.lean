import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two-dimensional braid (Yang–Baxter) defect for `B = F R F`

Fix `u v` with `u² + v² = 1`, `F = !![u, v; v, -u]`, `R = diag(a, b)`, `B = F R F`.
Put `Q = u²(a-b)² + ab` and `C = !![v², -uv; -uv, -v²]`.

* `braid_defect` (any commutative ring): `R B R - B R B = ((a-b) Q) • C`.
* `C_mul_C`: `C * C = v² • 1`.
* `braid_of_v_eq_zero`, `braid_iff_of_v_ne_zero` (over `ℂ`): if `v = 0` then
  `RBR = BRB` always; if `v ≠ 0` then `RBR = BRB ↔ a = b ∨ Q = 0`.
* Unitary phases (`q = a/b`): `Q_eq_zero_iff_phase` (`Q = 0 ↔ u²(q-1)² + q = 0` for `b ≠ 0`);
  for `‖q‖ = 1` and real `u ≠ 0`, `phase_eq_iff_re`: `u²(q-1)²+q = 0 ↔ Re q = 1 - 1/(2u²)`;
  `phase_exp_iff`: for `q = exp(iθ)` this is `cos θ = 1 - 1/(2u²)`;
  `phase_u_sq_ge`: a solution forces `u² ≥ 1/4`, i.e. `|u| ≥ 1/2`; `phase_half`: `|u| = 1/2`
  forces `q = -1`; `golden_phase` / `phase_golden_iff`: for `u = φ⁻¹`,
  `1 - 1/(2u²) = 1 - φ²/2 = (1-√5)/4 = cos(3π/5)`.
* `defect_norm` (l2 operator norm on `Matrix (Fin 2) (Fin 2) ℂ`, real `u v`):
  `‖RBR - BRB‖ = ‖a-b‖ · ‖Q‖ · |v|`; also `defect_conjTranspose_mul_self`:
  `(RBR-BRB)ᴴ (RBR-BRB) = (‖a-b‖² ‖Q‖² v²) • 1`, so both singular values equal `|a-b||Q||v|`.
-/

namespace APEX.Anyon

open Matrix

section Ring

variable {α : Type*} [CommRing α]

/-- `F = !![u, v; v, -u]`. -/
def Fm (u v : α) : Matrix (Fin 2) (Fin 2) α := !![u, v; v, -u]
/-- `R = diag(a, b)`. -/
def Rm (a b : α) : Matrix (Fin 2) (Fin 2) α := !![a, 0; 0, b]
/-- `B = F R F`. -/
def Bm (u v a b : α) : Matrix (Fin 2) (Fin 2) α := Fm u v * Rm a b * Fm u v
/-- `Q = u²(a-b)² + ab`. -/
def Qf (u a b : α) : α := u ^ 2 * (a - b) ^ 2 + a * b
/-- `C = !![v², -uv; -uv, -v²]`. -/
def Cm (u v : α) : Matrix (Fin 2) (Fin 2) α := !![v ^ 2, -u * v; -u * v, -v ^ 2]

/-- The braid defect identity. -/
theorem braid_defect (u v a b : α) (h : u ^ 2 + v ^ 2 = 1) :
    Rm a b * Bm u v a b * Rm a b - Bm u v a b * Rm a b * Bm u v a b
      = ((a - b) * Qf u a b) • Cm u v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rm, Bm, Fm, Cm, Qf]
  · linear_combination (-a * b ^ 2 * v ^ 2 - a ^ 3 * u ^ 2) * h
  · linear_combination (2 * a * b ^ 2 * u * v - 2 * a ^ 2 * b * u * v) * h
  · linear_combination (2 * a * b ^ 2 * u * v - 2 * a ^ 2 * b * u * v) * h
  · linear_combination (-b ^ 3 * u ^ 2 - a ^ 2 * b * v ^ 2) * h

theorem C_mul_C (u v : α) (h : u ^ 2 + v ^ 2 = 1) : Cm u v * Cm u v = v ^ 2 • (1 : Matrix _ _ α) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Cm, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination v ^ 2 * h
  · ring
  · ring
  · linear_combination v ^ 2 * h

end Ring

section Classification

theorem braid_of_v_eq_zero (u a b : ℂ) (h : u ^ 2 + 0 ^ 2 = 1) :
    Rm a b * Bm u 0 a b * Rm a b = Bm u 0 a b * Rm a b * Bm u 0 a b := by
  have := braid_defect u 0 a b h
  rw [← sub_eq_zero, this]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Cm]

theorem braid_iff_of_v_ne_zero (u v a b : ℂ) (h : u ^ 2 + v ^ 2 = 1) (hv : v ≠ 0) :
    Rm a b * Bm u v a b * Rm a b = Bm u v a b * Rm a b * Bm u v a b ↔ a = b ∨ Qf u a b = 0 := by
  rw [← sub_eq_zero, braid_defect u v a b h]
  constructor
  · intro H
    have h00 := congrFun (congrFun H 0) 0
    simp [Cm] at h00
    rcases h00 with (h1 | h1) | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr h1
    · exact absurd h1 hv
  · rintro (h1 | h1)
    · simp [h1]
    · simp [h1]

end Classification

section Phases

open Complex ComplexConjugate

theorem Q_eq_zero_iff_phase (u a b : ℂ) (hb : b ≠ 0) :
    Qf u a b = 0 ↔ u ^ 2 * (a / b - 1) ^ 2 + a / b = 0 := by
  have : u ^ 2 * (a / b - 1) ^ 2 + a / b = Qf u a b / b ^ 2 := by
    unfold Qf; field_simp
  rw [this, div_eq_zero_iff]; simp [hb]

/-- For `‖q‖ = 1` and real `u ≠ 0`: `u²(q-1)² + q = 0 ↔ Re q = 1 - 1/(2u²)`. -/
theorem phase_eq_iff_re (u : ℝ) (hu : u ≠ 0) (q : ℂ) (hq : ‖q‖ = 1) :
    (u : ℂ) ^ 2 * (q - 1) ^ 2 + q = 0 ↔ q.re = 1 - 1 / (2 * u ^ 2) := by
  have hqc : q * conj q = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hq]; simp
  have hre : q + conj q = 2 * (q.re : ℂ) := by
    rw [Complex.add_conj]; push_cast; ring
  have hu2 : (0 : ℝ) < u ^ 2 := by positivity
  -- key reformulation
  have key : (u : ℂ) ^ 2 * (q - 1) ^ 2 + q = 0 ↔ ((u ^ 2 * (2 * q.re - 2) + 1 : ℝ) : ℂ) = 0 := by
    push_cast
    rw [← hre]
    constructor
    · intro H
      linear_combination (conj q) * H + (-(u : ℂ) ^ 2 * q + 2 * (u : ℂ) ^ 2 - 1) * hqc
    · intro H
      linear_combination q * H - (u : ℂ) ^ 2 * hqc
  rw [key, Complex.ofReal_eq_zero]
  constructor
  · intro H; field_simp; linarith
  · intro H; rw [H]; field_simp; ring

theorem phase_exp_iff (u : ℝ) (hu : u ≠ 0) (θ : ℝ) :
    (u : ℂ) ^ 2 * (Complex.exp (θ * Complex.I) - 1) ^ 2 + Complex.exp (θ * Complex.I) = 0 ↔
      Real.cos θ = 1 - 1 / (2 * u ^ 2) := by
  rw [phase_eq_iff_re u hu _ (by simp),
    Complex.exp_ofReal_mul_I_re]

theorem phase_u_sq_ge (u : ℝ) (hu : u ≠ 0) (q : ℂ) (hq : ‖q‖ = 1)
    (h : (u : ℂ) ^ 2 * (q - 1) ^ 2 + q = 0) : 1 / 4 ≤ u ^ 2 ∧ 1 / 2 ≤ |u| := by
  have hre := (phase_eq_iff_re u hu q hq).mp h
  have h1 : -1 ≤ q.re := by
    have := Complex.abs_re_le_norm q; rw [hq] at this; exact (abs_le.mp this).1
  have hu2 : (0 : ℝ) < u ^ 2 := by positivity
  have h4 : 1 / 4 ≤ u ^ 2 := by
    rw [hre] at h1
    have : 1 / (2 * u ^ 2) ≤ 2 := by linarith
    rw [div_le_iff₀ (by positivity)] at this; linarith
  refine ⟨h4, ?_⟩
  have : (1 / 2 : ℝ) ^ 2 ≤ |u| ^ 2 := by rw [sq_abs]; linarith
  exact (pow_le_pow_iff_left₀ (by norm_num) (abs_nonneg u) (by norm_num)).mp this

theorem phase_half (u : ℝ) (hu : |u| = 1 / 2) (q : ℂ) (hq : ‖q‖ = 1)
    (h : (u : ℂ) ^ 2 * (q - 1) ^ 2 + q = 0) : q = -1 := by
  have hu0 : u ≠ 0 := by intro h0; rw [h0] at hu; norm_num at hu
  have hre := (phase_eq_iff_re u hu0 q hq).mp h
  have hu2 : u ^ 2 = 1 / 4 := by rw [← sq_abs, hu]; norm_num
  rw [hu2] at hre; norm_num at hre
  have hn : q.re * q.re + q.im * q.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hq]; norm_num
  rw [hre] at hn
  have him : q.im = 0 := by nlinarith
  apply Complex.ext <;> simp [hre, him]

open Real in
theorem cos_three_pi_div_five : Real.cos (3 * π / 5) = (1 - √5) / 4 := by
  have h1 : 3 * π / 5 = π - 2 * (π / 5) := by ring
  rw [h1, Real.cos_pi_sub, Real.cos_two_mul, Real.cos_pi_div_five]
  have : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (-1 / 8) * this

open Real in
/-- For `u = φ⁻¹`: `1 - 1/(2u²) = 1 - φ²/2 = (1 - √5)/4 = cos(3π/5)`. -/
theorem golden_phase :
    1 - 1 / (2 * goldenRatio⁻¹ ^ 2) = 1 - goldenRatio ^ 2 / 2 ∧
    1 - goldenRatio ^ 2 / 2 = (1 - √5) / 4 ∧
    1 - 1 / (2 * goldenRatio⁻¹ ^ 2) = Real.cos (3 * π / 5) := by
  have e1 : 1 - 1 / (2 * goldenRatio⁻¹ ^ 2) = 1 - goldenRatio ^ 2 / 2 := by
    have := goldenRatio_ne_zero; field_simp
  have e2 : 1 - goldenRatio ^ 2 / 2 = (1 - √5) / 4 := by
    rw [goldenRatio_sq]; unfold goldenRatio; ring
  exact ⟨e1, e2, by rw [e1, e2, cos_three_pi_div_five]⟩

open Real in
theorem phase_golden_iff (θ : ℝ) :
    ((goldenRatio⁻¹ : ℝ) : ℂ) ^ 2 * (Complex.exp (θ * Complex.I) - 1) ^ 2
        + Complex.exp (θ * Complex.I) = 0 ↔ Real.cos θ = Real.cos (3 * π / 5) := by
  rw [phase_exp_iff _ (inv_ne_zero goldenRatio_ne_zero), golden_phase.2.2]

end Phases

section Norm

open scoped Matrix.Norms.L2Operator

/-- `C₀ = !![v, -u; -u, -v]`, so that `C = v • C₀`. -/
def C0 (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(v : ℂ), -(u : ℂ); -(u : ℂ), -(v : ℂ)]

theorem C0_mem_unitary (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) :
    C0 u v ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  have hc : ((u : ℂ)) ^ 2 + (v : ℂ) ^ 2 = 1 := by exact_mod_cast h
  have hs : star (C0 u v) = C0 u v := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [C0]
  have hsq : C0 u v * C0 u v = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [C0, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hc
    · ring
    · ring
    · linear_combination hc
  rw [Unitary.mem_iff, hs]; exact ⟨hsq, hsq⟩

theorem norm_C0 (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) : ‖C0 u v‖ = 1 :=
  CStarRing.norm_of_mem_unitary (C0_mem_unitary u v h)

theorem defect_eq_smul_C0 (u v : ℝ) (a b : ℂ) (h : u ^ 2 + v ^ 2 = 1) :
    Rm a b * Bm (u : ℂ) v a b * Rm a b - Bm (u : ℂ) v a b * Rm a b * Bm (u : ℂ) v a b
      = ((a - b) * Qf (u : ℂ) a b * v) • C0 u v := by
  have hc : ((u : ℂ)) ^ 2 + (v : ℂ) ^ 2 = 1 := by exact_mod_cast h
  rw [braid_defect _ _ a b hc]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Cm, C0] <;> ring

/-- Exact l2-operator norm of the braid defect. -/
theorem defect_norm (u v : ℝ) (a b : ℂ) (h : u ^ 2 + v ^ 2 = 1) :
    ‖Rm a b * Bm (u : ℂ) v a b * Rm a b - Bm (u : ℂ) v a b * Rm a b * Bm (u : ℂ) v a b‖
      = ‖a - b‖ * ‖Qf (u : ℂ) a b‖ * |v| := by
  rw [defect_eq_smul_C0 u v a b h, norm_smul, norm_C0 u v h, mul_one, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]

/-- `Dᴴ D` is scalar, so both singular values of the defect equal `|a-b| |Q| |v|`. -/
theorem defect_conjTranspose_mul_self (u v : ℝ) (a b : ℂ) (h : u ^ 2 + v ^ 2 = 1) :
    let D := Rm a b * Bm (u : ℂ) v a b * Rm a b - Bm (u : ℂ) v a b * Rm a b * Bm (u : ℂ) v a b
    Dᴴ * D = (((‖a - b‖ * ‖Qf (u : ℂ) a b‖ * |v|) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro D
  have hU := C0_mem_unitary u v h
  rw [Unitary.mem_iff] at hU
  set c : ℂ := (a - b) * Qf (u : ℂ) a b * v
  have hD : D = c • C0 u v := defect_eq_smul_C0 u v a b h
  rw [hD, Matrix.conjTranspose_smul, ← Matrix.star_eq_conjTranspose, smul_mul_smul_comm, hU.1]
  congr 1
  rw [show star c = (starRingEnd ℂ) c from rfl, Complex.conj_mul']
  norm_cast
  simp only [c, norm_mul, Complex.norm_real, Real.norm_eq_abs]

end Norm


end APEX.Anyon
