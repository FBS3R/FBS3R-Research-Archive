/-
# Logical algebra of the spin-2 AKLT plaquette qutrit (2026-10-28)

Source: *Measurement-Free Encoded Qubit Control and a Two-Local Qutrit Obstruction in a
Spin-2 AKLT Plaquette*, Theorem "All-times protected qubit universality".

The paper gives the logical actions `A = PH₂P|_C`, `B = PH₃P|_C` as explicit rational 3×3
matrices and the involution `R` (antidiagonal swap).  Machine-checked here, over `ℚ`:
* `A_comm_R`, `B_comm_R` : `AR = RA`, `BR = RB`;
* `C1_eq`, `C2_eq`, `C3_eq` : explicit values of `[A,B]`, `[A,[A,B]]`, `[B,[A,B]]`
  (all commute with `R`, `bracket_comm_R`);
* `five_independent` : `A, B, [A,B], [A,[A,B]], [B,[A,B]]` are linearly independent —
  so they span the full 5-dimensional commutant of `R` (`gl₂ ⊕ gl₁`), matching the
  stated `u(2) ⊕ u(1)`;
* `odd_line` : on the `R = −1` line `(1,0,−1)` the energies are `69` and `−534`.

Not checked: the 625-dimensional leakage map (rank 6, kernel 18) and the identities
`QH₂P = QH₃P = 0` in the full physical space.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace FBS3R.AKLT

open Matrix

def R : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
def A : Matrix (Fin 3) (Fin 3) ℚ := !![69, 14, 0; 54, 96, 54; 0, 14, 69]
def B : Matrix (Fin 3) (Fin 3) ℚ := !![-453, -52, 81; -729/2, -642, -729/2; 81, -52, -453]
def C1 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-2295, -2376, -2295; 9477/2, 4590, 9477/2; -2295, -2376, -2295]
def C2 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![194643, 192672, 194643; -735561/2, -389286, -735561/2; 194643, 192672, 194643]
def C3 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-1112454, -1118880, -1112454; 2066715, 2224908, 2066715; -1112454, -1118880, -1112454]

macro "mat_tac" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
      simp [R, A, B, C1, C2, C3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num))

theorem R_sq : R * R = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [R, Matrix.mul_apply, Fin.sum_univ_succ]

theorem A_comm_R : A * R = R * A := by mat_tac
theorem B_comm_R : B * R = R * B := by mat_tac
theorem C1_eq : A * B - B * A = C1 := by mat_tac
theorem C2_eq : A * C1 - C1 * A = C2 := by mat_tac
theorem C3_eq : B * C1 - C1 * B = C3 := by mat_tac

theorem bracket_comm_R : C1 * R = R * C1 ∧ C2 * R = R * C2 ∧ C3 * R = R * C3 := by
  refine ⟨?_, ?_, ?_⟩ <;> mat_tac

/-- The five logical generators are linearly independent over `ℚ`. -/
theorem five_independent (a b c d e : ℚ)
    (h : a • A + b • B + c • C1 + d • C2 + e • C3 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [A, B, C1, C2, C3] at h00 h01 h02 h10 h11
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Energies on the odd line `R = −1`. -/
theorem odd_line :
    A *ᵥ ![1, 0, -1] = (69 : ℚ) • ![1, 0, -1] ∧ B *ᵥ ![1, 0, -1] = (-534 : ℚ) • ![1, 0, -1] ∧
      R *ᵥ ![1, 0, -1] = (-1 : ℚ) • ![1, 0, -1] := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [A, B, R, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

end FBS3R.AKLT
