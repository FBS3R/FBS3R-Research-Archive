import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Fibonacci anyon model: F-matrix, pentagon and hexagon equations

Labels are `Bool`: `false = 1` (vacuum), `true = τ`; fusion `τ ⊗ τ = 1 ⊕ τ`, encoded by
`adm a b c` (`N_{ab}^c = 1` iff the number of `τ`'s among `a, b, c` is not exactly one).
`φ = Real.goldenRatio`, `sφ = √(φ⁻¹) = φ^{-1/2}` (`sqrtInv_eq_rpow`).

**F-symbols** `Fsym a b c d e f = [F^{abc}_d]_{e f}` (real), where `e` labels the channel
`(a b) → e, (e c) → d` and `f` the channel `(b c) → f, (a f) → d`.
On `a = b = c = d = τ` it is the matrix `Fmat = !![φ⁻¹, φ^{-1/2}; φ^{-1/2}, -φ⁻¹]`
(rows `e`, columns `f`, basis order `1, τ`; `Fmat_entry`); every other F-symbol is `1` if all
four vertices are admissible and `0` otherwise.

**R-symbols** `Rsym a b c = R^{ab}_c` (complex): `R^{ττ}_1 = e^{-4πi/5}`, `R^{ττ}_τ = e^{3πi/5}`,
`1` on the other admissible triples and `0` on inadmissible ones.

## Main results
* `Fmat_mul_self : Fmat * Fmat = 1`, `Fmat_transpose : Fmatᵀ = Fmat`,
  `Fmat_orthogonal : Fmatᵀ * Fmat = 1 ∧ Fmat * Fmatᵀ = 1`,
  `Fmat_mem_orthogonalGroup : Fmat ∈ Matrix.orthogonalGroup (Fin 2) ℝ`.
* `pentagon` (all `2⁹` label choices):
  `F^{fcd}_{e;gl} F^{abl}_{e;fk} = Σ_h F^{abc}_{g;fh} F^{ahd}_{e;gk} F^{bcd}_{k;hl}`
  with `F^{abc}_{d;xy} := Fsym a b c d x y`.
* `hexagon` (all `2⁶` label choices; Bonderson's convention):
  `R^{ac}_e [F^{acb}_d]_{eg} R^{bc}_g = Σ_f [F^{cab}_d]_{ef} R^{fc}_d [F^{abc}_d]_{fg}`,
  and `hexagon_inv`: the same identity with every `R` replaced by `R⁻¹`.
* `hexagon_block`: the `τττ→τ` instance in 2×2 form, `R F R = F · diag(1, R^{ττ}_τ) · F`
  with `R = diag(R^{ττ}_1, R^{ττ}_τ)`.
* `braid_relation`: `σ₁ = R`, `σ₂ = F R F` satisfy `σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂`.
* `σ₁_pow_ten`, `σ₂_pow_ten`: `σ₁¹⁰ = σ₂¹⁰ = 1`; `σ₁_pow_scalar_iff`, `σ₂_pow_scalar_iff`:
  `σᵢᵏ` is a scalar matrix iff `10 ∣ k` (projective order exactly 10).

## Method
The equations are reduced, by the ring-hom-like evaluation `evK` (`evK_add`, `evK_mul`), to
identities in a small computable model `K = ℤ[ζ]/(Φ₁₀(ζ)) [s]/(s² - (ζ² - ζ³))` with
`ζ ↦ e^{iπ/5}`, `s ↦ φ^{-1/2}` (using `2 cos(π/5) = φ`, so `φ⁻¹ = ζ² - ζ³`), and those finitely
many identities are checked by `decide +kernel` (kernel evaluation, no `native_decide`).
The real pentagon is obtained from the complex one by injectivity of `ℝ → ℂ`.
-/

namespace APEX.Anyon.Fibonacci

open Complex Real Matrix

/-! ## A computable model of `ℤ[ζ₁₀][s]`, used only as a proof device -/

/-- `c0 + c1 ζ + c2 ζ² + c3 ζ³` in `ℤ[ζ]/(ζ⁴ - ζ³ + ζ² - ζ + 1)`, `ζ` a primitive 10th root of 1. -/
structure Z4 where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
deriving DecidableEq

namespace Z4
def add (x y : Z4) : Z4 := ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3⟩
/-- Product, reduced with `ζ⁴ = -1 + ζ - ζ² + ζ³`, `ζ⁵ = -1`, `ζ⁶ = -ζ`. -/
def mul (x y : Z4) : Z4 :=
  ⟨x.c0 * y.c0 - (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1) - (x.c2 * y.c3 + x.c3 * y.c2),
   (x.c0 * y.c1 + x.c1 * y.c0) + (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1) - x.c3 * y.c3,
   (x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0) - (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1),
   (x.c0 * y.c3 + x.c1 * y.c2 + x.c2 * y.c1 + x.c3 * y.c0)
     + (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1)⟩
instance : Add Z4 := ⟨add⟩
instance : Mul Z4 := ⟨mul⟩
instance : Zero Z4 := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Z4 := ⟨⟨1, 0, 0, 0⟩⟩
end Z4

/-- `x + y s` with `s² = t := ζ² - ζ³` (`t` evaluates to `φ⁻¹`, `s` to `√φ⁻¹`). -/
structure K where
  x : Z4
  y : Z4
deriving DecidableEq

namespace K
def t : Z4 := ⟨0, 0, 1, -1⟩
instance : Add K := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
instance : Mul K := ⟨fun a b => ⟨a.x * b.x + t * (a.y * b.y), a.x * b.y + a.y * b.x⟩⟩
instance : Zero K := ⟨⟨0, 0⟩⟩
instance : One K := ⟨⟨1, 0⟩⟩
end K

/-! ## Fusion rules and generic F- and R-symbols -/

/-- Labels: `false = 1` (vacuum), `true = τ`. `adm a b c` iff `N_{ab}^c = 1`, i.e. the number
of `τ`'s among `a b c` is not exactly one (`1⊗1 = 1`, `1⊗τ = τ⊗1 = τ`, `τ⊗τ = 1 ⊕ τ`). -/
def adm (a b c : Bool) : Bool := !(xor (xor a b) c) || (a && b && c)

/-- Generic F-symbol `[F^{abc}_d]_{e f}` with values `o` (admissible one-dimensional move),
`z` (inadmissible), and on the `τττ → τ` block the matrix `!![p, s; s, m]`. Here `e` is the
intermediate channel of `(a b) → e`, `(e c) → d` and `f` that of `(b c) → f`, `(a f) → d`. -/
def Fgen {α : Type*} (o z p s m : α) (a b c d e f : Bool) : α :=
  if a && b && c && d then (if e then (if f then m else s) else (if f then s else p))
  else if adm a b e && adm e c d && adm b c f && adm a f d then o else z

/-- Generic R-symbol `R^{ab}_c`: `r1 = R^{ττ}_1`, `rt = R^{ττ}_τ`, `o` on other admissible
triples, `z` on inadmissible ones. -/
def Rgen {α : Type*} (o z r1 rt : α) (a b c : Bool) : α :=
  if a && b then (if c then rt else r1) else if adm a b c then o else z

theorem Fgen_map {α β : Type*} (g : α → β) (o z p s m : α) (a b c d e f : Bool) :
    g (Fgen o z p s m a b c d e f) = Fgen (g o) (g z) (g p) (g s) (g m) a b c d e f := by
  unfold Fgen; split_ifs <;> rfl

theorem Rgen_map {α β : Type*} (g : α → β) (o z r1 rt : α) (a b c : Bool) :
    g (Rgen o z r1 rt a b c) = Rgen (g o) (g z) (g r1) (g rt) a b c := by
  unfold Rgen; split_ifs <;> rfl

/-! ## The Fibonacci data -/

/-- `φ^{-1/2}`, defined as `√(φ⁻¹)`; see `sqrtInv_eq_rpow`. -/
noncomputable def sφ : ℝ := √(goldenRatio⁻¹)

/-- The Fibonacci F-symbols `[F^{abc}_d]_{ef} ∈ ℝ`: on `τττ → τ` the matrix
`!![φ⁻¹, φ^{-1/2}; φ^{-1/2}, -φ⁻¹]`, otherwise `1` if admissible and `0` if not. -/
noncomputable def Fsym : Bool → Bool → Bool → Bool → Bool → Bool → ℝ :=
  Fgen 1 0 goldenRatio⁻¹ sφ (-goldenRatio⁻¹)

/-- The Fibonacci R-symbols `R^{ab}_c ∈ ℂ`: `R^{ττ}_1 = e^{-4πi/5}`, `R^{ττ}_τ = e^{3πi/5}`,
`1` on the other admissible triples and `0` on inadmissible ones. -/
noncomputable def Rsym : Bool → Bool → Bool → ℂ :=
  Rgen 1 0 (Complex.exp (-4 * π / 5 * I)) (Complex.exp (3 * π / 5 * I))

/-- The F-matrix on the `τττ → τ` space (basis `1, τ`). -/
noncomputable def Fmat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![goldenRatio⁻¹, sφ; sφ, -goldenRatio⁻¹]

/-! ## Real identities -/

theorem inv_gold_eq : goldenRatio⁻¹ = goldenRatio - 1 := by
  rw [inv_goldenRatio, ← one_sub_goldenConj]; ring

theorem inv_gold_sq : goldenRatio⁻¹ ^ 2 + goldenRatio⁻¹ = 1 := by
  rw [inv_gold_eq]; linear_combination goldenRatio_sq

theorem inv_gold_pos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos

theorem sφ_sq : sφ ^ 2 = goldenRatio⁻¹ := Real.sq_sqrt inv_gold_pos.le

theorem sqrtInv_eq_rpow : sφ = goldenRatio ^ (-(1 / 2 : ℝ)) := by
  rw [sφ, Real.sqrt_eq_rpow, Real.inv_rpow goldenRatio_pos.le, Real.rpow_neg goldenRatio_pos.le]

theorem Fmat_entry (i j : Fin 2) :
    Fmat i j = Fsym true true true true (i = 1) (j = 1) := by
  fin_cases i <;> fin_cases j <;> simp [Fmat, Fsym, Fgen]

theorem F2_aux (p s : ℝ) (hs : s ^ 2 = p) (hp : p ^ 2 + p = 1) :
    !![p, s; s, -p] * !![p, s; s, -p] = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hs + hp
  · ring
  · ring
  · linear_combination hs + hp

/-- `F² = 1`. -/
theorem Fmat_mul_self : Fmat * Fmat = 1 := F2_aux _ _ sφ_sq inv_gold_sq

/-- `F` is symmetric. -/
theorem Fmat_transpose : Fmatᵀ = Fmat := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- `F` is real orthogonal (= unitary over `ℝ`). -/
theorem Fmat_orthogonal : Fmatᵀ * Fmat = 1 ∧ Fmat * Fmatᵀ = 1 := by
  rw [Fmat_transpose]; exact ⟨Fmat_mul_self, Fmat_mul_self⟩

theorem Fmat_mem_orthogonalGroup : Fmat ∈ Matrix.orthogonalGroup (Fin 2) ℝ :=
  (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mpr Fmat_orthogonal.2

/-! ## Complex evaluation of the model -/

/-- `ζ = e^{iπ/5}`. -/
noncomputable def ζ : ℂ := Complex.exp (π / 5 * I)
noncomputable def ζbar : ℂ := Complex.exp (-(π / 5) * I)
noncomputable def σ : ℂ := (sφ : ℂ)

theorem ζ_mul_ζbar : ζ * ζbar = 1 := by
  rw [ζ, ζbar, ← Complex.exp_add]; ring_nf; exact Complex.exp_zero

theorem gold_eq_ζ : (goldenRatio : ℂ) = ζ + ζbar := by
  have h : goldenRatio = 2 * Real.cos (π / 5) := by
    rw [Real.cos_pi_div_five]; unfold goldenRatio; ring
  rw [h, ζ, ζbar]; push_cast
  rw [Complex.two_cos]

theorem hΦ : ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 := by
  have h1 := gold_eq_ζ
  have h2 := ζ_mul_ζbar
  have h3 : (goldenRatio : ℂ) ^ 2 = goldenRatio + 1 := by exact_mod_cast goldenRatio_sq
  linear_combination ζ ^ 2 * h3 - ζ ^ 2 * ((goldenRatio : ℂ) + ζ + ζbar - 1) * h1
    - (2 * ζ ^ 2 + ζ * ζbar + 1 - ζ) * h2

theorem ζ_pow_five : ζ ^ 5 = -1 := by linear_combination (ζ + 1) * hΦ

theorem inv_gold_eq_ζ : ((goldenRatio⁻¹ : ℝ) : ℂ) = ζ ^ 2 - ζ ^ 3 := by
  have h : ((goldenRatio⁻¹ : ℝ) : ℂ) = (goldenRatio : ℂ) - 1 := by
    rw [inv_gold_eq]; push_cast; ring
  rw [h, gold_eq_ζ]
  have h2 := ζ_mul_ζbar
  linear_combination ζbar * hΦ + (ζbar - (ζ + ζbar - 1 - (ζ ^ 2 - ζ ^ 3))) * h2

theorem σ_sq : σ ^ 2 = ζ ^ 2 - ζ ^ 3 := by
  rw [σ, ← inv_gold_eq_ζ, ← sφ_sq]; push_cast; rfl

noncomputable def evZ (z : Z4) : ℂ := z.c0 + z.c1 * ζ + z.c2 * ζ ^ 2 + z.c3 * ζ ^ 3
noncomputable def evK (k : K) : ℂ := evZ k.x + evZ k.y * σ

theorem evZ_add (x y : Z4) : evZ (x + y) = evZ x + evZ y := by
  show evZ (Z4.add x y) = _
  simp only [evZ, Z4.add]; push_cast; ring

theorem evZ_mul (x y : Z4) : evZ (x * y) = evZ x * evZ y := by
  show evZ (Z4.mul x y) = _
  simp only [evZ, Z4.mul]; push_cast
  linear_combination
    (-(((x.c1 : ℂ) * y.c3 + (x.c2 : ℂ) * y.c2 + (x.c3 : ℂ) * y.c1)
      + ((x.c2 : ℂ) * y.c3 + (x.c3 : ℂ) * y.c2) * (ζ + 1)
      + ((x.c3 : ℂ) * y.c3) * ζ * (ζ + 1))) * hΦ

theorem evZ_t : evZ K.t = ζ ^ 2 - ζ ^ 3 := by simp [evZ, K.t]; ring

theorem evK_add (a b : K) : evK (a + b) = evK a + evK b := by
  show evZ (a.x + b.x) + evZ (a.y + b.y) * σ = _
  rw [evZ_add, evZ_add, evK, evK]; ring

theorem evK_mul (a b : K) : evK (a * b) = evK a * evK b := by
  show evZ (a.x * b.x + K.t * (a.y * b.y)) + evZ (a.x * b.y + a.y * b.x) * σ = _
  simp only [evZ_add, evZ_mul, evZ_t, evK]
  linear_combination (-(evZ a.y * evZ b.y)) * σ_sq

/-! ## The model in `K` and the transfer lemmas -/

def FK : Bool → Bool → Bool → Bool → Bool → Bool → K :=
  Fgen 1 0 ⟨K.t, 0⟩ ⟨0, 1⟩ ⟨⟨0, 0, -1, 1⟩, 0⟩

/-- `R^{ττ}_1 ↦ -ζ`, `R^{ττ}_τ ↦ ζ³`. -/
def RK : Bool → Bool → Bool → K :=
  Rgen 1 0 ⟨⟨0, -1, 0, 0⟩, 0⟩ ⟨⟨0, 0, 0, 1⟩, 0⟩

/-- Inverses: `(-ζ)⁻¹ = ζ⁴ = -1 + ζ - ζ² + ζ³`, `(ζ³)⁻¹ = -ζ²`. -/
def RKi : Bool → Bool → Bool → K :=
  Rgen 1 0 ⟨⟨-1, 1, -1, 1⟩, 0⟩ ⟨⟨0, 0, -1, 0⟩, 0⟩

theorem Fsym_cast (a b c d e f : Bool) : ((Fsym a b c d e f : ℝ) : ℂ) = evK (FK a b c d e f) := by
  unfold Fsym FK
  rw [Fgen_map Complex.ofReal, Fgen_map evK]
  have h1 : ((1 : ℝ) : ℂ) = evK 1 := by
    show _ = evZ ⟨1, 0, 0, 0⟩ + evZ ⟨0, 0, 0, 0⟩ * σ; simp [evZ]
  have h0 : ((0 : ℝ) : ℂ) = evK 0 := by
    show _ = evZ ⟨0, 0, 0, 0⟩ + evZ ⟨0, 0, 0, 0⟩ * σ; simp [evZ]
  have hp : ((goldenRatio⁻¹ : ℝ) : ℂ) = evK ⟨K.t, 0⟩ := by
    show _ = evZ K.t + evZ ⟨0, 0, 0, 0⟩ * σ; rw [evZ_t, inv_gold_eq_ζ]; simp [evZ]
  have hs : ((sφ : ℝ) : ℂ) = evK ⟨0, 1⟩ := by
    show _ = evZ ⟨0, 0, 0, 0⟩ + evZ ⟨1, 0, 0, 0⟩ * σ; simp [evZ, σ]
  have hm : ((-goldenRatio⁻¹ : ℝ) : ℂ) = evK ⟨⟨0, 0, -1, 1⟩, 0⟩ := by
    show _ = evZ ⟨0, 0, -1, 1⟩ + evZ ⟨0, 0, 0, 0⟩ * σ
    rw [Complex.ofReal_neg, inv_gold_eq_ζ]; simp [evZ]; ring
  rw [h1, h0, hp, hs, hm]

theorem exp_three : Complex.exp (3 * π / 5 * I) = ζ ^ 3 := by
  rw [ζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem exp_neg_four : Complex.exp (-4 * π / 5 * I) = -ζ := by
  rw [show (-4 * (π : ℂ) / 5 * I) = π / 5 * I - π * I by ring, Complex.exp_sub,
    Complex.exp_pi_mul_I, ζ]; ring

theorem Rsym_eq (a b c : Bool) : Rsym a b c = evK (RK a b c) := by
  unfold Rsym RK
  rw [Rgen_map evK]
  have h1 : (1 : ℂ) = evK 1 := by
    show _ = evZ ⟨1, 0, 0, 0⟩ + evZ ⟨0, 0, 0, 0⟩ * σ; simp [evZ]
  have h0 : (0 : ℂ) = evK 0 := by
    show _ = evZ ⟨0, 0, 0, 0⟩ + evZ ⟨0, 0, 0, 0⟩ * σ; simp [evZ]
  have hr1 : Complex.exp (-4 * π / 5 * I) = evK ⟨⟨0, -1, 0, 0⟩, 0⟩ := by
    show _ = evZ ⟨0, -1, 0, 0⟩ + evZ ⟨0, 0, 0, 0⟩ * σ; rw [exp_neg_four]; simp [evZ]
  have hrt : Complex.exp (3 * π / 5 * I) = evK ⟨⟨0, 0, 0, 1⟩, 0⟩ := by
    show _ = evZ ⟨0, 0, 0, 1⟩ + evZ ⟨0, 0, 0, 0⟩ * σ; rw [exp_three]; simp [evZ]
  rw [h1, h0, hr1, hrt]

theorem Rsym_inv_eq (a b c : Bool) : (Rsym a b c)⁻¹ = evK (RKi a b c) := by
  unfold Rsym RKi
  rw [Rgen_map (·⁻¹), Rgen_map evK]
  have h1 : (1 : ℂ)⁻¹ = evK 1 := by
    show _ = evZ ⟨1, 0, 0, 0⟩ + evZ ⟨0, 0, 0, 0⟩ * σ; simp [evZ]
  have h0 : (0 : ℂ)⁻¹ = evK 0 := by
    show _ = evZ ⟨0, 0, 0, 0⟩ + evZ ⟨0, 0, 0, 0⟩ * σ; simp [evZ]
  have hr1 : (Complex.exp (-4 * π / 5 * I))⁻¹ = evK ⟨⟨-1, 1, -1, 1⟩, 0⟩ := by
    show _ = evZ ⟨-1, 1, -1, 1⟩ + evZ ⟨0, 0, 0, 0⟩ * σ
    rw [exp_neg_four]; apply inv_eq_of_mul_eq_one_right; simp [evZ]
    linear_combination -hΦ
  have hrt : (Complex.exp (3 * π / 5 * I))⁻¹ = evK ⟨⟨0, 0, -1, 0⟩, 0⟩ := by
    show _ = evZ ⟨0, 0, -1, 0⟩ + evZ ⟨0, 0, 0, 0⟩ * σ
    rw [exp_three]; apply inv_eq_of_mul_eq_one_right; simp [evZ]
    linear_combination -ζ_pow_five
  simp only [h1, h0, hr1, hrt]

/-! ## The consistency equations in `K` (by kernel computation) -/

theorem pentagonK : ∀ a b c d e f g k l : Bool,
    FK f c d e g l * FK a b l e f k =
      FK a b c g f true * FK a true d e g k * FK b c d k true l +
      FK a b c g f false * FK a false d e g k * FK b c d k false l := by
  decide +kernel

theorem hexagonK : ∀ a b c d e g : Bool,
    RK a c e * FK a c b d e g * RK b c g =
      FK c a b d e true * RK true c d * FK a b c d true g +
      FK c a b d e false * RK false c d * FK a b c d false g := by
  decide +kernel

theorem hexagonK_inv : ∀ a b c d e g : Bool,
    RKi a c e * FK a c b d e g * RKi b c g =
      FK c a b d e true * RKi true c d * FK a b c d true g +
      FK c a b d e false * RKi false c d * FK a b c d false g := by
  decide +kernel

/-! ## Pentagon and hexagon equations -/

/-- **Pentagon equation** for the Fibonacci F-symbols, all label choices:
`F^{fcd}_{e;gl} F^{abl}_{e;fk} = Σ_h F^{abc}_{g;fh} F^{ahd}_{e;gk} F^{bcd}_{k;hl}`,
where `F^{abc}_{d;xy} = Fsym a b c d x y`. -/
theorem pentagon (a b c d e f g k l : Bool) :
    Fsym f c d e g l * Fsym a b l e f k =
      ∑ h : Bool, Fsym a b c g f h * Fsym a h d e g k * Fsym b c d k h l := by
  apply Complex.ofReal_injective
  rw [Fintype.sum_bool]
  push_cast
  simp only [Fsym_cast, ← evK_mul, ← evK_add]
  exact congrArg evK (pentagonK a b c d e f g k l)

/-- **Hexagon equation** (Bonderson's convention):
`R^{ac}_e [F^{acb}_d]_{eg} R^{bc}_g = Σ_f [F^{cab}_d]_{ef} R^{fc}_d [F^{abc}_d]_{fg}`. -/
theorem hexagon (a b c d e g : Bool) :
    Rsym a c e * (Fsym a c b d e g : ℂ) * Rsym b c g =
      ∑ f : Bool, (Fsym c a b d e f : ℂ) * Rsym f c d * (Fsym a b c d f g : ℂ) := by
  rw [Fintype.sum_bool]
  simp only [Fsym_cast, Rsym_eq, ← evK_mul, ← evK_add]
  exact congrArg evK (hexagonK a b c d e g)

/-- **Inverse hexagon equation** (the same with `R ↦ R⁻¹`). -/
theorem hexagon_inv (a b c d e g : Bool) :
    (Rsym a c e)⁻¹ * (Fsym a c b d e g : ℂ) * (Rsym b c g)⁻¹ =
      ∑ f : Bool, (Fsym c a b d e f : ℂ) * (Rsym f c d)⁻¹ * (Fsym a b c d f g : ℂ) := by
  rw [Fintype.sum_bool]
  simp only [Fsym_cast, Rsym_inv_eq, ← evK_mul, ← evK_add]
  exact congrArg evK (hexagonK_inv a b c d e g)


/-! ## 2×2 block form, braid generators and their order -/

/-- `F = !![u, v; v, -u]` over a commutative ring. -/
def Fm2 {α : Type*} [CommRing α] (u v : α) : Matrix (Fin 2) (Fin 2) α := !![u, v; v, -u]
/-- `diag(a, b)`. -/
def Rm2 {α : Type*} [CommRing α] (a b : α) : Matrix (Fin 2) (Fin 2) α := !![a, 0; 0, b]

theorem Fm2_mul_self {α : Type*} [CommRing α] (u v : α) (h : u ^ 2 + v ^ 2 = 1) :
    Fm2 u v * Fm2 u v = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Fm2, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

/-- The braid defect identity (same as `APEX.Anyon.braid_defect` in `Braid2D.lean`, restated
here because that module is not importable without a build). -/
theorem braid_defect2 {α : Type*} [CommRing α] (u v a b : α) (h : u ^ 2 + v ^ 2 = 1) :
    Rm2 a b * (Fm2 u v * Rm2 a b * Fm2 u v) * Rm2 a b
      - (Fm2 u v * Rm2 a b * Fm2 u v) * Rm2 a b * (Fm2 u v * Rm2 a b * Fm2 u v)
      = ((a - b) * (u ^ 2 * (a - b) ^ 2 + a * b)) • !![v ^ 2, -u * v; -u * v, -v ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rm2, Fm2]
  · linear_combination (-a * b ^ 2 * v ^ 2 - a ^ 3 * u ^ 2) * h
  · linear_combination (2 * a * b ^ 2 * u * v - 2 * a ^ 2 * b * u * v) * h
  · linear_combination (2 * a * b ^ 2 * u * v - 2 * a ^ 2 * b * u * v) * h
  · linear_combination (-b ^ 3 * u ^ 2 - a ^ 2 * b * v ^ 2) * h

/-- The F-matrix over `ℂ`. -/
noncomputable def Fc : Matrix (Fin 2) (Fin 2) ℂ :=
  Fm2 ((goldenRatio⁻¹ : ℝ) : ℂ) (sφ : ℂ)

theorem Fc_eq_map : Fc = Fmat.map Complex.ofReal := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Fc, Fm2, Fmat]

theorem Fc_unit : ((goldenRatio⁻¹ : ℝ) : ℂ) ^ 2 + (sφ : ℂ) ^ 2 = 1 := by
  exact_mod_cast (by rw [sφ_sq]; linear_combination inv_gold_sq : goldenRatio⁻¹ ^ 2 + sφ ^ 2 = 1)

theorem Fc_mul_self : Fc * Fc = 1 := Fm2_mul_self _ _ Fc_unit

/-- The braid generator `σ₁ = R = diag(R^{ττ}_1, R^{ττ}_τ) = diag(e^{-4πi/5}, e^{3πi/5})`. -/
noncomputable def σ₁ : Matrix (Fin 2) (Fin 2) ℂ :=
  Rm2 (Complex.exp (-4 * π / 5 * I)) (Complex.exp (3 * π / 5 * I))

/-- The braid generator `σ₂ = F R F`. -/
noncomputable def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := Fc * σ₁ * Fc

/-- `diag(R^{τ1}_τ, R^{ττ}_τ) = diag(1, e^{3πi/5})` (the `R^{fτ}_τ` in the hexagon sum). -/
noncomputable def Rτ : Matrix (Fin 2) (Fin 2) ℂ := Rm2 1 (Complex.exp (3 * π / 5 * I))

theorem σ₁_entries : σ₁ = Rm2 (Rsym true true false) (Rsym true true true) := rfl

/-- **Hexagon, 2×2 block form** (`a = b = c = d = τ`): `R F R = F · diag(1, R^{ττ}_τ) · F`. -/
theorem hexagon_block : σ₁ * Fc * σ₁ = Fc * Rτ * Fc := by
  ext i j
  have H := hexagon true true true true (i = 1) (j = 1)
  fin_cases i <;> fin_cases j <;>
    simp [Fsym, Fgen, adm, Rsym, Rgen] at H <;>
    simp [σ₁, Rτ, Fc, Rm2, Fm2, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination H

/-- **Braid (Yang–Baxter) relation** `σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂`. -/
theorem braid_relation : σ₁ * σ₂ * σ₁ = σ₂ * σ₁ * σ₂ := by
  rw [← sub_eq_zero, σ₂, Fc, σ₁, braid_defect2 _ _ _ _ Fc_unit, exp_neg_four, exp_three,
    inv_gold_eq_ζ]
  have hQ : (ζ ^ 2 - ζ ^ 3) ^ 2 * (-ζ - ζ ^ 3) ^ 2 + -ζ * ζ ^ 3 = 0 := by
    linear_combination (-ζ ^ 4 - ζ ^ 5 + ζ ^ 6 - ζ ^ 7 + ζ ^ 8) * hΦ
  rw [hQ, mul_zero, zero_smul]

theorem σ₁_eq_diagonal : σ₁ = Matrix.diagonal ![-ζ, ζ ^ 3] := by
  rw [σ₁, exp_neg_four, exp_three]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Rm2]

theorem ζ_pow_ten : ζ ^ 10 = 1 := by
  rw [show (10 : ℕ) = 5 * 2 from rfl, pow_mul, ζ_pow_five]; norm_num

theorem σ₁_pow_ten : σ₁ ^ 10 = 1 := by
  rw [σ₁_eq_diagonal, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1; ext i; fin_cases i
  · show (-ζ) ^ 10 = 1
    rw [neg_pow, ζ_pow_ten]; norm_num
  · show (ζ ^ 3) ^ 10 = 1
    rw [← pow_mul, show (3 * 10 : ℕ) = 10 * 3 from rfl, pow_mul, ζ_pow_ten, one_pow]

theorem σ₂_pow (n : ℕ) : σ₂ ^ n = Fc * σ₁ ^ n * Fc := by
  induction n with
  | zero => simp [Fc_mul_self]
  | succ n ih =>
    rw [pow_succ, ih, σ₂, pow_succ]
    calc Fc * σ₁ ^ n * Fc * (Fc * σ₁ * Fc) = Fc * σ₁ ^ n * (Fc * Fc) * σ₁ * Fc := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [Fc_mul_self, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem σ₂_pow_ten : σ₂ ^ 10 = 1 := by
  rw [σ₂_pow, σ₁_pow_ten, Matrix.mul_one, Fc_mul_self]

theorem ζ_pow_eq_one_iff (n : ℕ) : ζ ^ n = 1 ↔ 10 ∣ n := by
  constructor
  · intro h
    rw [ζ, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hm' : ((n * π / 5 : ℝ) : ℂ) = ((m * (2 * π) : ℝ) : ℂ) := by
      push_cast
      apply mul_right_cancel₀ Complex.I_ne_zero
      linear_combination hm
    have hr : (n : ℝ) * π / 5 = m * (2 * π) := Complex.ofReal_injective hm'
    have hr2 : ((n : ℤ) : ℝ) = ((10 * m : ℤ) : ℝ) := by
      push_cast
      have := Real.pi_pos
      field_simp at hr
      nlinarith
    have : (n : ℤ) = 10 * m := by exact_mod_cast hr2
    omega
  · rintro ⟨k, rfl⟩
    rw [pow_mul, ζ_pow_ten, one_pow]

/-- **Projective order of `σ₁` is exactly 10**: `σ₁ᵏ` is a scalar matrix iff `10 ∣ k`. -/
theorem σ₁_pow_scalar_iff (k : ℕ) :
    (∃ c : ℂ, σ₁ ^ k = c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ↔ 10 ∣ k := by
  constructor
  · rintro ⟨c, hc⟩
    rw [σ₁_eq_diagonal, Matrix.diagonal_pow] at hc
    have h0 := congrFun (congrFun hc 0) 0
    have h1 := congrFun (congrFun hc 1) 1
    simp at h0 h1
    have heq : (-ζ) ^ k = (ζ ^ 3) ^ k := h0.trans h1.symm
    have h3 : (ζ ^ 3) ^ k = 1 := by
      have e1 : ((-ζ) * (-ζ ^ 2)) ^ k = ((ζ ^ 3) * (-ζ ^ 2)) ^ k := by
        rw [mul_pow, mul_pow, heq]
      have e2 : (-ζ) * (-ζ ^ 2) = ζ ^ 3 := by ring
      have e3 : (ζ ^ 3) * (-ζ ^ 2) = 1 := by linear_combination -ζ_pow_five
      rw [e2, e3, one_pow] at e1; exact e1
    rw [← pow_mul, ζ_pow_eq_one_iff] at h3
    omega
  · rintro ⟨m, rfl⟩
    exact ⟨1, by rw [pow_mul, σ₁_pow_ten, one_pow, one_smul]⟩

/-- **Projective order of `σ₂` is exactly 10**. -/
theorem σ₂_pow_scalar_iff (k : ℕ) :
    (∃ c : ℂ, σ₂ ^ k = c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ↔ 10 ∣ k := by
  rw [← σ₁_pow_scalar_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have : Fc * σ₂ ^ k * Fc = σ₁ ^ k := by
      rw [σ₂_pow]; simp only [← Matrix.mul_assoc, Fc_mul_self, Matrix.one_mul]
      rw [Matrix.mul_assoc, Fc_mul_self, Matrix.mul_one]
    rw [← this, hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Fc_mul_self]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [σ₂_pow, hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Fc_mul_self]

end APEX.Anyon.Fibonacci

