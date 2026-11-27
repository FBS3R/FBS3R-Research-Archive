import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Spin-2 square plaquette ("AKLT plaquette"): kernel-checked singlet-sector facts

Setting: four spin-2 sites, one-site basis `e_k = u^(4-k) v^k`, `Sz e_k = (2-k) e_k`,
`S₊ e_k = k e_(k-1)`, `S₋ e_k = (4-k) e_(k+1)`, Gram metric `G = diag(1/binom(4,k))`;
`X_ij = S_i·S_j`, `P_ij = X(X+3)(X+5)(X+6)/2520`, `H_square = P₀₁ + P₀₂ + P₁₃ + P₂₃`.
To stay in `ℤ` we work with `Y_ij = 2 X_ij`, so `Y(Y+6)(Y+10)(Y+12) = 40320 P`,
`4 H₂ = Y₀₃² − Y₀₁² − Y₀₂² − 32(Y₀₁+Y₀₂)`, `8 H₃ = Y₀₃³ + ∑_{j=1,2}(Y₀ⱼ³ + 38Y₀ⱼ² + 608Y₀ⱼ)`.
A vector of the 625-dimensional space is its coordinate function `V = Fin 5⁴ → ℤ`
(scaling by nonzero integers changes no kernel / invariance statement).

Proved here (no `sorry`, no `native_decide`; large finite checks by `decide +kernel`):
* Part A (one site): `[S₊,S₋] = 2Sz`, `[Sz,S±] = ±S±`, Casimir `S² = 6`,
  `Sz` is `G`-self-adjoint and the `G`-adjoint of `S₊` is `S₋`.
* Part B: the coordinate formula for `2 S₁·S₂` equals the 25×25 matrix
  `2Sz⊗Sz + S₊⊗S₋ + S₋⊗S₊` (`pairY_eq_matrix`); the six `Y_ij` and total `S₊,S₋,Sz` are
  `ℤ`-linear maps on `V`.
* Part C: five explicit integer vectors `sv0..sv4` (output of `aklt_cert.py`) are singlets
  (killed by total `S₊`, `S₋`, `Sz`), are linearly independent (`emb_injective`), and on their span
  every `Y_ij` acts by an explicit 5×5 integer matrix `N_ij` (`intertw_Y01` … `intertw_Y23`).
  This is the **restriction step**, checked in the kernel on all 625 coordinates.
* Part D: inside the span of these singlets, `ker H_square` is exactly
  `{∑ c_k sv_k | c₀ = c₄ = 0}`, a 3-dimensional subspace (`Hsq_emb_eq_zero_iff`, `code_eq_kernel`);
  `H₂` and `H₃` map this code into itself (`Q H₂ P = Q H₃ P = 0`), and `H₂` is not scalar on it.

NOT proved here: that `sv0..sv4` span the *whole* singlet sector (dimension 5; certified only in
`aklt_cert.py`, by exact rank of total `S₊ : (Jz=0) → (Jz=1)`), the leakage-map rank/kernel,
the logical-image dimensions, and the logical Lie algebra `u(2)⊕u(1)` (all Python-only).
-/

namespace APEX.AKLT

open Matrix

/-- Coordinates of a 4-site vector in the product basis `e_a ⊗ e_b ⊗ e_c ⊗ e_d`. -/
abbrev V := Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℤ

/-! ## Part A: one-site spin-2 operators (5×5) -/

/-- `Sz e_k = (2-k) e_k` (column `j` = image of `e_j`). -/
def Sz : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, -2]
/-- `S₊ e_k = k e_(k-1)`. -/
def Sp : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 1, 0, 0, 0; 0, 0, 2, 0, 0; 0, 0, 0, 3, 0; 0, 0, 0, 0, 4; 0, 0, 0, 0, 0]
/-- `S₋ e_k = (4-k) e_(k+1)`. -/
def Sm : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 0, 0, 0, 0; 4, 0, 0, 0, 0; 0, 3, 0, 0, 0; 0, 0, 2, 0, 0; 0, 0, 0, 1, 0]
/-- Gram metric `G = diag(1/binom(4,k))`. -/
def G : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1, 0, 0, 0, 0; 0, 1/4, 0, 0, 0; 0, 0, 1/6, 0, 0; 0, 0, 0, 1/4, 0; 0, 0, 0, 0, 1]

/-- `[S₊, S₋] = 2 Sz`. -/
theorem comm_Sp_Sm : Sp * Sm - Sm * Sp = 2 • Sz := by decide +kernel
theorem comm_Sz_Sp : Sz * Sp - Sp * Sz = Sp := by decide +kernel
theorem comm_Sz_Sm : Sz * Sm - Sm * Sz = -Sm := by decide +kernel
/-- Casimir: `2 (Sz² + (S₊S₋ + S₋S₊)/2) = 12`, i.e. `S² = s(s+1) = 6`. -/
theorem casimir : 2 • (Sz * Sz) + Sp * Sm + Sm * Sp = 12 • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
  decide +kernel

/-- `Sz` is `G`-self-adjoint: `Szᵀ G = G Sz`. -/
theorem Sz_selfAdjoint : (Sz.map (Int.cast : ℤ → ℚ))ᵀ * G = G * Sz.map (Int.cast : ℤ → ℚ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Sz, G, Matrix.mul_apply, Fin.sum_univ_five]
/-- The `G`-adjoint of `S₊` is `S₋`: `S₊ᵀ G = G S₋`; hence `Sx = (S₊+S₋)/2` and
`Sy = (S₊-S₋)/(2i)` are `G`-self-adjoint. -/
theorem Sp_adjoint_eq_Sm :
    (Sp.map (Int.cast : ℤ → ℚ))ᵀ * G = G * Sm.map (Int.cast : ℤ → ℚ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Sp, Sm, G, Matrix.mul_apply, Fin.sum_univ_five] <;> norm_num
/-- singlet basis vector number 0 (coordinates in the product basis). -/
def sv0 : V := ![![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 1], ![0, 0, 0, -4, 0], ![0, 0, 6, 0, 0], ![0, -4, 0, 0, 0], ![1, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, -4], ![0, 0, 0, 16, 0], ![0, 0, -24, 0, 0], ![0, 16, 0, 0, 0], ![-4, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 6], ![0, 0, 0, -24, 0], ![0, 0, 36, 0, 0], ![0, -24, 0, 0, 0], ![6, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, -4], ![0, 0, 0, 16, 0], ![0, 0, -24, 0, 0], ![0, 16, 0, 0, 0], ![-4, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 1], ![0, 0, 0, -4, 0], ![0, 0, 6, 0, 0], ![0, -4, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]

/-- singlet basis vector number 1 (coordinates in the product basis). -/
def sv1 : V := ![![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, -3, 0], ![0, 0, 3, 0, 0], ![0, -1, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, -1, 0], ![0, 0, 3, 0, 0], ![0, -3, 0, 0, 0], ![1, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, -3], ![0, 0, 0, 9, 0], ![0, 0, -9, 0, 0], ![0, 3, 0, 0, 0]], ![![0, 0, 0, 0, -1], ![0, 0, 0, 6, 0], ![0, 0, -12, 0, 0], ![0, 10, 0, 0, 0], ![-3, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, -3, 0, 0], ![0, 3, 0, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 3], ![0, 0, 0, -9, 0], ![0, 0, 9, 0, 0], ![0, -3, 0, 0, 0]], ![![0, 0, 0, 0, 3], ![0, 0, 0, -12, 0], ![0, 0, 18, 0, 0], ![0, -12, 0, 0, 0], ![3, 0, 0, 0, 0]], ![![0, 0, 0, -3, 0], ![0, 0, 9, 0, 0], ![0, -9, 0, 0, 0], ![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, -1], ![0, 0, 0, 3, 0], ![0, 0, -3, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, 0, 0, -3], ![0, 0, 0, 10, 0], ![0, 0, -12, 0, 0], ![0, 6, 0, 0, 0], ![-1, 0, 0, 0, 0]], ![![0, 0, 0, 3, 0], ![0, 0, -9, 0, 0], ![0, 9, 0, 0, 0], ![-3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 1], ![0, 0, 0, -3, 0], ![0, 0, 3, 0, 0], ![0, -1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, -1, 0], ![0, 0, 3, 0, 0], ![0, -3, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]

/-- singlet basis vector number 2 (coordinates in the product basis). -/
def sv2 : V := ![![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, -2, 0], ![0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, -2, 0], ![0, 0, 4, 0, 0], ![0, -2, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, -2, 0, 0, 0], ![1, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, -2], ![0, 0, 0, 4, 0], ![0, 0, -2, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, -2], ![0, 0, 0, 8, 0], ![0, 0, -10, 0, 0], ![0, 4, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 4, 0], ![0, 0, -10, 0, 0], ![0, 8, 0, 0, 0], ![-2, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, -2, 0, 0], ![0, 4, 0, 0, 0], ![-2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, -2, 0], ![0, 0, 1, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 4], ![0, 0, 0, -10, 0], ![0, 0, 8, 0, 0], ![0, -2, 0, 0, 0]], ![![0, 0, 0, 0, 1], ![0, 0, 0, -10, 0], ![0, 0, 18, 0, 0], ![0, -10, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, -2, 0], ![0, 0, 8, 0, 0], ![0, -10, 0, 0, 0], ![4, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, -2, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, -2], ![0, 0, 0, 4, 0], ![0, 0, -2, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, -2], ![0, 0, 0, 8, 0], ![0, 0, -10, 0, 0], ![0, 4, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 4, 0], ![0, 0, -10, 0, 0], ![0, 8, 0, 0, 0], ![-2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, -2, 0, 0], ![0, 4, 0, 0, 0], ![-2, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 1], ![0, 0, 0, -2, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, -2, 0], ![0, 0, 4, 0, 0], ![0, -2, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, -2, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]

/-- singlet basis vector number 3 (coordinates in the product basis). -/
def sv3 : V := ![![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, -1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, -3, 0], ![0, 0, 3, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, -3, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, -1, 0, 0, 0], ![1, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, -1], ![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, -3], ![0, 0, 0, 6, 0], ![0, 0, -3, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 9, 0], ![0, 0, -12, 0, 0], ![0, 3, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, -9, 0, 0], ![0, 10, 0, 0, 0], ![-1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![-3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 3], ![0, 0, 0, -3, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 3], ![0, 0, 0, -12, 0], ![0, 0, 9, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, -9, 0], ![0, 0, 18, 0, 0], ![0, -9, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 9, 0, 0], ![0, -12, 0, 0, 0], ![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, -3, 0, 0, 0], ![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, -3], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, -1], ![0, 0, 0, 10, 0], ![0, 0, -9, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 3, 0], ![0, 0, -12, 0, 0], ![0, 9, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, -3, 0, 0], ![0, 6, 0, 0, 0], ![-3, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 1], ![0, 0, 0, -1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, -3, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 3, 0, 0], ![0, -3, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, -1, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]

/-- singlet basis vector number 4 (coordinates in the product basis). -/
def sv4 : V := ![![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, -4, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 6, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, -4, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, -4], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 16, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, -24, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 16, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![-4, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 6], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, -24, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 36, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, -24, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![6, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, -4], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 16, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, -24, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 16, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![-4, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, -4, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 6, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, -4, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]

/-- `2 X_01` restricted to the singlet span, in the basis `sv0..sv4`. -/
def N01 : Matrix (Fin 5) (Fin 5) ℤ := !![-12, -1, 0, 0, 0; 0, -10, -4, 0, 0; 0, 0, -6, -9, 0; 0, 0, 0, 0, -16; 0, 0, 0, 0, 8]

/-- `2 X_02` restricted to the singlet span, in the basis `sv0..sv4`. -/
def N02 : Matrix (Fin 5) (Fin 5) ℤ := !![8, 0, 0, 0, 0; -16, 0, 0, 0, 0; 0, -9, -6, 0, 0; 0, 0, -4, -10, 0; 0, 0, 0, -1, -12]

/-- `2 X_03` restricted to the singlet span, in the basis `sv0..sv4`. -/
def N03 : Matrix (Fin 5) (Fin 5) ℤ := !![-8, 1, 0, 0, 0; 16, -2, 4, 0, 0; 0, 9, 0, 9, 0; 0, 0, 4, -2, 16; 0, 0, 0, 1, -8]

/-- `2 X_12` restricted to the singlet span, in the basis `sv0..sv4`. -/
def N12 : Matrix (Fin 5) (Fin 5) ℤ := !![-8, 1, 0, 0, 0; 16, -2, 4, 0, 0; 0, 9, 0, 9, 0; 0, 0, 4, -2, 16; 0, 0, 0, 1, -8]

/-- `2 X_13` restricted to the singlet span, in the basis `sv0..sv4`. -/
def N13 : Matrix (Fin 5) (Fin 5) ℤ := !![8, 0, 0, 0, 0; -16, 0, 0, 0, 0; 0, -9, -6, 0, 0; 0, 0, -4, -10, 0; 0, 0, 0, -1, -12]

/-- `2 X_23` restricted to the singlet span, in the basis `sv0..sv4`. -/
def N23 : Matrix (Fin 5) (Fin 5) ℤ := !![-12, -1, 0, 0, 0; 0, -10, -4, 0, 0; 0, 0, -6, -9, 0; 0, 0, 0, 0, -16; 0, 0, 0, 0, 8]

-- Hmat_val = !![80640, 0, 0, 0, 1152; -161280, 0, 0, 0, -23040; 103680, 0, 0, 0, 103680; -23040, 0, 0, 0, -161280; 1152, 0, 0, 0, 80640]

-- H2m_val = !![0, 0, 0, 0, 0; 480, 276, 56, 0, 0; 0, 216, 384, 216, 0; 0, 0, 56, 276, 480; 0, 0, 0, 0, 0]

-- H3m_val = !![3456, 0, 0, 0, 0; -13440, -3624, -416, 648, 0; 4320, -2916, -5136, -2916, 4320; 0, 648, -416, -3624, -13440; 0, 0, 0, 0, 3456]

/-! ## Part B: four-site operators on the product space (as explicit coordinate formulas) -/

/-- `S₊` on one site, in coordinates: `(S₊ f)(m) = (m+1) f(m+1)` (from `S₊ e_k = k e_(k-1)`). -/
def sp1 (f : Fin 5 → ℤ) (m : Fin 5) : ℤ := if m.val < 4 then ((m.val : ℤ) + 1) * f (m + 1) else 0
/-- `S₋` on one site, in coordinates: `(S₋ f)(m) = (5-m) f(m-1)` (from `S₋ e_k = (4-k) e_(k+1)`). -/
def sm1 (f : Fin 5 → ℤ) (m : Fin 5) : ℤ := if 0 < m.val then (5 - (m.val : ℤ)) * f (m - 1) else 0

/-- `2 S₁·S₂ = 2 Sz⊗Sz + S₊⊗S₋ + S₋⊗S₊` on two sites, in coordinates. -/
def pairY (f : Fin 5 → Fin 5 → ℤ) (a b : Fin 5) : ℤ :=
  2 * (2 - (a.val : ℤ)) * (2 - (b.val : ℤ)) * f a b
    + sp1 (fun x => sm1 (f x) b) a + sm1 (fun x => sp1 (f x) b) a

/-- The coordinate formula `pairY` is exactly the action of the 25×25 matrix
`2 Sz⊗Sz + S₊⊗S₋ + S₋⊗S₊` built from the one-site matrices of Part A. -/
theorem pairY_eq_matrix (f : Fin 5 → Fin 5 → ℤ) (a b : Fin 5) :
    pairY f a b = ∑ a' : Fin 5, ∑ b' : Fin 5,
      (2 * Sz a a' * Sz b b' + Sp a a' * Sm b b' + Sm a a' * Sp b b') * f a' b' := by
  fin_cases a <;> fin_cases b <;>
    simp [pairY, sp1, sm1, Fin.sum_univ_five, Sz, Sp, Sm] <;> ring_nf

/-- `2 X_ij` on the 625-dimensional space, for the six pairs. -/
def Y01f (ψ : V) : V := fun a b c d => pairY (fun x y => ψ x y c d) a b
def Y02f (ψ : V) : V := fun a b c d => pairY (fun x y => ψ x b y d) a c
def Y03f (ψ : V) : V := fun a b c d => pairY (fun x y => ψ x b c y) a d
def Y12f (ψ : V) : V := fun a b c d => pairY (fun x y => ψ a x y d) b c
def Y13f (ψ : V) : V := fun a b c d => pairY (fun x y => ψ a x c y) b d
def Y23f (ψ : V) : V := fun a b c d => pairY (fun x y => ψ a b x y) c d

/-- total `S₊`, `S₋`, `Sz` on four sites. -/
def SpTotf (ψ : V) : V := fun a b c d =>
  sp1 (fun x => ψ x b c d) a + sp1 (fun x => ψ a x c d) b + sp1 (fun x => ψ a b x d) c
    + sp1 (fun x => ψ a b c x) d
def SmTotf (ψ : V) : V := fun a b c d =>
  sm1 (fun x => ψ x b c d) a + sm1 (fun x => ψ a x c d) b + sm1 (fun x => ψ a b x d) c
    + sm1 (fun x => ψ a b c x) d
def SzTotf (ψ : V) : V := fun a b c d =>
  (8 - (a.val : ℤ) - b.val - c.val - d.val) * ψ a b c d

macro "lin_tac" : tactic => `(tactic| (
  intro ψ φ; funext a b c d
  simp only [Y01f, Y02f, Y03f, Y12f, Y13f, Y23f, SpTotf, SmTotf, SzTotf, pairY, sp1, sm1,
    Pi.add_apply]
  (try split_ifs) <;> ring))

/-- an additive map of `ℤ`-modules, as a `ℤ`-linear endomorphism -/
def endOf (f : V → V) (hf : ∀ ψ φ, f (ψ + φ) = f ψ + f φ) : Module.End ℤ V :=
  (AddMonoidHom.mk' f hf).toIntLinearMap

@[simp] theorem endOf_apply (f : V → V) (hf) (ψ : V) : endOf f hf ψ = f ψ := rfl

def Y01 : Module.End ℤ V := endOf Y01f (by lin_tac)
def Y02 : Module.End ℤ V := endOf Y02f (by lin_tac)
def Y03 : Module.End ℤ V := endOf Y03f (by lin_tac)
def Y12 : Module.End ℤ V := endOf Y12f (by lin_tac)
def Y13 : Module.End ℤ V := endOf Y13f (by lin_tac)
def Y23 : Module.End ℤ V := endOf Y23f (by lin_tac)
def SpTot : Module.End ℤ V := endOf SpTotf (by lin_tac)
def SmTot : Module.End ℤ V := endOf SmTotf (by lin_tac)
def SzTot : Module.End ℤ V := endOf SzTotf (by lin_tac)

/-! ## Part C: the five explicit singlets and the restriction of `X_ij` to their span -/

/-- the five singlet vectors as a family -/
def sv : Fin 5 → V := ![sv0, sv1, sv2, sv3, sv4]

/-- every `sv k` is annihilated by total `S₊`, `S₋` and `Sz` (kernel computation, 3125 points each). -/
theorem sv_SpTot : ∀ k a b c d : Fin 5, SpTotf (sv k) a b c d = 0 := by decide +kernel
theorem sv_SmTot : ∀ k a b c d : Fin 5, SmTotf (sv k) a b c d = 0 := by decide +kernel
theorem sv_SzTot : ∀ k a b c d : Fin 5, SzTotf (sv k) a b c d = 0 := by decide +kernel

/-- the coordinate map `ℤ⁵ → V`, `c ↦ ∑ c k • sv k`. -/
def emb : (Fin 5 → ℤ) →ₗ[ℤ] V := Fintype.linearCombination ℤ sv

theorem emb_apply (c : Fin 5 → ℤ) : emb c = ∑ k, c k • sv k :=
  Fintype.linearCombination_apply ℤ sv c

/-- evaluation points: `sv k` at `(0, 4-l, l, 4)` is `δ_kl`. -/
theorem sv_points : ∀ k l : Fin 5, sv k 0 (4 - l) l 4 = if k = l then 1 else 0 := by
  decide +kernel

theorem emb_point (c : Fin 5 → ℤ) (l : Fin 5) : emb c 0 (4 - l) l 4 = c l := by
  rw [emb_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sv_points, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem emb_injective : Function.Injective emb := by
  intro c c' h
  funext l
  rw [← emb_point c l, ← emb_point c' l, h]

/-- Every vector of the span is a total-spin singlet. -/
theorem emb_singlet (c : Fin 5 → ℤ) :
    SpTot (emb c) = 0 ∧ SmTot (emb c) = 0 ∧ SzTot (emb c) = 0 := by
  have key : ∀ (A : Module.End ℤ V), (∀ k, A (sv k) = 0) → A (emb c) = 0 := by
    intro A hA
    rw [emb_apply, map_sum]
    simp only [map_zsmul, hA, smul_zero, Finset.sum_const_zero]
  refine ⟨key _ fun k => ?_, key _ fun k => ?_, key _ fun k => ?_⟩ <;> funext a b c d
  · exact sv_SpTot k a b c d
  · exact sv_SmTot k a b c d
  · exact sv_SzTot k a b c d

theorem emb_singlet_ne_zero (c : Fin 5 → ℤ) (hc : c ≠ 0) : emb c ≠ 0 := by
  intro h
  exact hc (emb_injective (h.trans (map_zero emb).symm))

/-- `A` restricted to the span of the singlets has matrix `N` in the basis `sv`. -/
def Intertw (A : Module.End ℤ V) (N : Matrix (Fin 5) (Fin 5) ℤ) : Prop :=
  ∀ c, A (emb c) = emb (N *ᵥ c)

theorem Intertw.mul {A B : Module.End ℤ V} {M N : Matrix (Fin 5) (Fin 5) ℤ}
    (hA : Intertw A M) (hB : Intertw B N) : Intertw (A * B) (M * N) := by
  intro c
  rw [mul_apply_eq_comp, hB, hA, Matrix.mulVec_mulVec]

theorem Intertw.add {A B : Module.End ℤ V} {M N : Matrix (Fin 5) (Fin 5) ℤ}
    (hA : Intertw A M) (hB : Intertw B N) : Intertw (A + B) (M + N) := by
  intro c
  rw [LinearMap.add_apply, hA, hB, Matrix.add_mulVec, map_add]

theorem Intertw.sub {A B : Module.End ℤ V} {M N : Matrix (Fin 5) (Fin 5) ℤ}
    (hA : Intertw A M) (hB : Intertw B N) : Intertw (A - B) (M - N) := by
  intro c
  rw [LinearMap.sub_apply, hA, hB, Matrix.sub_mulVec, map_sub]

theorem Intertw.smul {A : Module.End ℤ V} {M : Matrix (Fin 5) (Fin 5) ℤ} (k : ℤ)
    (hA : Intertw A M) : Intertw (k • A) (k • M) := by
  intro c
  rw [LinearMap.smul_apply, hA, Matrix.smul_mulVec, map_smul]

theorem Intertw.one : Intertw 1 1 := by
  intro c
  rw [one_apply_eq_self, Matrix.one_mulVec]

/-- explicit linear combination of the five singlets (used by the kernel checks). -/
def comb (c : Fin 5 → ℤ) : V := fun a b e d =>
  c 0 * sv0 a b e d + c 1 * sv1 a b e d + c 2 * sv2 a b e d + c 3 * sv3 a b e d + c 4 * sv4 a b e d

theorem Intertw.of_table (A : Module.End ℤ V) (N : Matrix (Fin 5) (Fin 5) ℤ)
    (h : ∀ i a b c d : Fin 5, A (sv i) a b c d = comb (fun l => N l i) a b c d) :
    Intertw A N := by
  have hl : A ∘ₗ emb = emb ∘ₗ N.mulVecLin := by
    ext i : 1
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.single_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one]
    rw [emb, Fintype.linearCombination_apply_single, one_smul, ← emb, emb_apply]
    funext a b c d
    rw [h i a b c d]
    simp [comb, Fin.sum_univ_five, sv, Matrix.col]
  intro c
  exact LinearMap.congr_fun hl c

/-- **Restriction step** (kernel-checked on all 5 × 625 coordinates): on the span of the five
singlets, `2 X_ij` acts by the explicit integer matrix `N_ij`, for all six pairs. -/
theorem intertw_Y01 : Intertw Y01 N01 := Intertw.of_table _ _ (by decide +kernel)
theorem intertw_Y02 : Intertw Y02 N02 := Intertw.of_table _ _ (by decide +kernel)
theorem intertw_Y03 : Intertw Y03 N03 := Intertw.of_table _ _ (by decide +kernel)
theorem intertw_Y12 : Intertw Y12 N12 := Intertw.of_table _ _ (by decide +kernel)
theorem intertw_Y13 : Intertw Y13 N13 := Intertw.of_table _ _ (by decide +kernel)
theorem intertw_Y23 : Intertw Y23 N23 := Intertw.of_table _ _ (by decide +kernel)

/-! ## Part D: the plaquette Hamiltonian, its singlet kernel, and `H₂`, `H₃` -/

/-- `Y(Y+6)(Y+10)(Y+12)`; with `Y = 2X` this is `16 X(X+3)(X+5)(X+6) = 40320 · P`. -/
def P4 (A : Module.End ℤ V) : Module.End ℤ V :=
  A * (A + (6 : ℤ) • 1) * (A + (10 : ℤ) • 1) * (A + (12 : ℤ) • 1)
def P4m (N : Matrix (Fin 5) (Fin 5) ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  N * (N + (6 : ℤ) • 1) * (N + (10 : ℤ) • 1) * (N + (12 : ℤ) • 1)

theorem Intertw.P4 {A : Module.End ℤ V} {N : Matrix (Fin 5) (Fin 5) ℤ} (h : Intertw A N) :
    Intertw (P4 A) (P4m N) :=
  (((h.mul (h.add (Intertw.one.smul 6))).mul (h.add (Intertw.one.smul 10))).mul
    (h.add (Intertw.one.smul 12)))

/-- `40320 · H_square = 40320 (P₀₁ + P₀₂ + P₁₃ + P₂₃)` on the 625-dimensional space. -/
def Hsq : Module.End ℤ V := P4 Y01 + P4 Y02 + P4 Y13 + P4 Y23
def Hmat : Matrix (Fin 5) (Fin 5) ℤ := P4m N01 + P4m N02 + P4m N13 + P4m N23

theorem intertw_Hsq : Intertw Hsq Hmat :=
  ((intertw_Y01.P4.add intertw_Y02.P4).add intertw_Y13.P4).add intertw_Y23.P4

theorem Hmat_eq : Hmat = !![80640, 0, 0, 0, 1152; -161280, 0, 0, 0, -23040;
    103680, 0, 0, 0, 103680; -23040, 0, 0, 0, -161280; 1152, 0, 0, 0, 80640] := by
  decide +kernel

/-- **Singlet code space.** A vector of the singlet span is annihilated by `H_square` iff its
coordinates 0 and 4 vanish; the kernel is the image of the 3-dimensional coordinate subspace
`{c | c 0 = 0 ∧ c 4 = 0}` under the injective map `emb`. -/
theorem Hsq_emb_eq_zero_iff (c : Fin 5 → ℤ) : Hsq (emb c) = 0 ↔ c 0 = 0 ∧ c 4 = 0 := by
  rw [intertw_Hsq c, ← (map_zero emb), emb_injective.eq_iff, Hmat_eq]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h4 := congrFun h 4
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five] at h0 h4
    omega
  · rintro ⟨h0, h4⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, h0, h4]

/-- The code vectors `sv1, sv2, sv3` (nonzero, linearly independent singlets) lie in `ker H_square`. -/
theorem code_basis (k : Fin 5) (hk0 : k ≠ 0) (hk4 : k ≠ 4) : Hsq (sv k) = 0 := by
  have : sv k = emb (Pi.single k 1) := by
    rw [emb, Fintype.linearCombination_apply_single, one_smul]
  rw [this, Hsq_emb_eq_zero_iff]
  simp [Ne.symm hk0, Ne.symm hk4]

/-- `4 H₂ = Y₀₃² − Y₀₁² − Y₀₂² − 32 (Y₀₁ + Y₀₂)`  (i.e. `H₂ = X₀₃² − X₀₁² − X₀₂² − 16(X₀₁+X₀₂)`). -/
def H2op : Module.End ℤ V := Y03 * Y03 - Y01 * Y01 - Y02 * Y02 - (32 : ℤ) • (Y01 + Y02)
def H2m : Matrix (Fin 5) (Fin 5) ℤ := N03 * N03 - N01 * N01 - N02 * N02 - (32 : ℤ) • (N01 + N02)

/-- `8 H₃ = Y₀₃³ + ∑_{j=1,2} (Y₀ⱼ³ + 38 Y₀ⱼ² + 608 Y₀ⱼ)`
(i.e. `H₃ = X₀₃³ + ∑ (X₀ⱼ³ + 19 X₀ⱼ² + 152 X₀ⱼ)`). -/
def H3op : Module.End ℤ V :=
  Y03 * Y03 * Y03 + (Y01 * Y01 * Y01 + (38 : ℤ) • (Y01 * Y01) + (608 : ℤ) • Y01)
    + (Y02 * Y02 * Y02 + (38 : ℤ) • (Y02 * Y02) + (608 : ℤ) • Y02)
def H3m : Matrix (Fin 5) (Fin 5) ℤ :=
  N03 * N03 * N03 + (N01 * N01 * N01 + (38 : ℤ) • (N01 * N01) + (608 : ℤ) • N01)
    + (N02 * N02 * N02 + (38 : ℤ) • (N02 * N02) + (608 : ℤ) • N02)

theorem intertw_H2 : Intertw H2op H2m :=
  (((intertw_Y03.mul intertw_Y03).sub (intertw_Y01.mul intertw_Y01)).sub
    (intertw_Y02.mul intertw_Y02)).sub ((intertw_Y01.add intertw_Y02).smul 32)

theorem intertw_H3 : Intertw H3op H3m :=
  ((intertw_Y03.mul intertw_Y03).mul intertw_Y03).add
    ((((intertw_Y01.mul intertw_Y01).mul intertw_Y01).add
      ((intertw_Y01.mul intertw_Y01).smul 38)).add (intertw_Y01.smul 608)) |>.add
    ((((intertw_Y02.mul intertw_Y02).mul intertw_Y02).add
      ((intertw_Y02.mul intertw_Y02).smul 38)).add (intertw_Y02.smul 608))

theorem H2m_eq : H2m = !![0, 0, 0, 0, 0; 480, 276, 56, 0, 0; 0, 216, 384, 216, 0;
    0, 0, 56, 276, 480; 0, 0, 0, 0, 0] := by decide +kernel

theorem H3m_eq : H3m = !![3456, 0, 0, 0, 0; -13440, -3624, -416, 648, 0;
    4320, -2916, -5136, -2916, 4320; 0, 648, -416, -3624, -13440; 0, 0, 0, 0, 3456] := by
  decide +kernel

/-- The code space `C = {emb c | c 0 = 0 ∧ c 4 = 0} = ker H_square ∩ span(singlets)`. -/
def Code : Set V := {ψ | ∃ c : Fin 5 → ℤ, c 0 = 0 ∧ c 4 = 0 ∧ ψ = emb c}

theorem code_eq_kernel (ψ : V) : ψ ∈ Code ↔ (∃ c, ψ = emb c) ∧ Hsq ψ = 0 := by
  constructor
  · rintro ⟨c, h0, h4, rfl⟩
    exact ⟨⟨c, rfl⟩, (Hsq_emb_eq_zero_iff c).2 ⟨h0, h4⟩⟩
  · rintro ⟨⟨c, rfl⟩, h⟩
    obtain ⟨h0, h4⟩ := (Hsq_emb_eq_zero_iff c).1 h
    exact ⟨c, h0, h4, rfl⟩

/-- **`Q H₂ P = 0`**: `H₂` maps the singlet code space into itself. -/
theorem H2_preserves_code (ψ : V) (hψ : ψ ∈ Code) : H2op ψ ∈ Code := by
  obtain ⟨c, h0, h4, rfl⟩ := hψ
  refine ⟨H2m *ᵥ c, ?_, ?_, intertw_H2 c⟩ <;>
    simp [H2m_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_five, h0, h4]

/-- **`Q H₃ P = 0`**: `H₃` maps the singlet code space into itself. -/
theorem H3_preserves_code (ψ : V) (hψ : ψ ∈ Code) : H3op ψ ∈ Code := by
  obtain ⟨c, h0, h4, rfl⟩ := hψ
  refine ⟨H3m *ᵥ c, ?_, ?_, intertw_H3 c⟩ <;>
    simp [H3m_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_five, h0, h4]

/-- `H₂` acts non-trivially (non-scalar) on the code: `4H₂ (sv1) ≠ λ sv1` for every `λ`. -/
theorem H2_not_scalar_on_code : ∀ l : ℤ, H2op (sv 1) ≠ l • sv 1 := by
  intro l h
  have e : sv 1 = emb (Pi.single 1 1) := by
    rw [emb, Fintype.linearCombination_apply_single, one_smul]
  rw [e, intertw_H2, ← map_smul, emb_injective.eq_iff, H2m_eq] at h
  have h2 := congrFun h 2
  simp [Matrix.mulVec, dotProduct, Pi.single_apply] at h2

end APEX.AKLT

