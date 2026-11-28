import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Scale consistency (coarse-graining) layer of the "unified law"

**Scope.** This file is the *abstract consistency layer* only. It formalises multi-scale state
spaces linked by coarse-graining maps `R_{ℓ'←ℓ}` and the consistency condition
`R_{ℓ'←ℓ} ∘ U_ℓ(t) = U_{ℓ'}(t) ∘ R_{ℓ'←ℓ}`. It derives **no physical law** and makes **no
prediction** that distinguishes GR, QFT or ΛCDM (or anything else). In §5 we prove that the
consistency condition by itself does not determine the state space at all.

All results are proved without `sorry`, custom axioms or `native_decide`.

## 1. Linear finite-dimensional / bounded-operator version
* `comp_pow_of_comp`, `mul_pow_of_mul`, `mul_pow_iff`: discrete time, `R T = T' R ⇒ R T^k = T'^k R`
  (operators resp. rectangular matrices over any semiring), and the converse at `k = 1`.
* `map_exp_eq_of_pow`, `eq_of_map_exp_smul`: abstract lemmas for continuous linear maps out of
  complete normed `ℝ`-algebras (power series / derivative at `t = 0`).
* `comp_exp_iff`: for Banach spaces `E, F` and bounded `R : E → F`, `A : E → E`, `A' : F → F`:
  `(∀ t, R ∘ exp(tA) = exp(tA') ∘ R) ↔ R ∘ A = A' ∘ R`.
* `matrix_mul_exp_iff`: the same for real matrices `R : m×n`, `A : n×n`, `A' : m×m` with
  `NormedSpace.exp` (the matrix exponential): `(∀ t, R exp(tA) = exp(tA') R) ↔ R A = A' R`.

## 2. Defect accumulation (discrete Duhamel)
* `defect R T T' = R T − T' R`; `defect_pow_succ` (exact one-step recursion);
* `norm_defect_pow_le`: `‖R T^k − T'^k R‖ ≤ ∑_{j<k} ‖T'‖^{k-1-j} ‖R T − T' R‖ ‖T‖^j`;
* `norm_defect_pow_le_of_contraction`: for `‖T‖, ‖T'‖ ≤ 1`, `‖R T^k − T'^k R‖ ≤ k ‖R T − T' R‖`;
* `norm_defect_pow_le_two_mul`: also `≤ 2‖R‖` (so linear growth must saturate);
* sharpness: `shift_defect_grows_linearly`: on `Fin N → ℝ` (sup norm) with the shift contraction
  `S` and the position operator `X`, `‖X S^k − S^k X‖ = k ‖X S − S X‖ = k` for all `k < N`
  (via the ring identity `commutator_pow_of_commutator_eq_self`: `[X,S] = S ⇒ [X,S^k] = k S^k`).

## 3. Composition (renormalisation-group / category structure)
* `Consistent R U U'` (all `t`); `Consistent.comp`, `consistent_one`;
* `norm_defect_comp_le`:
  `‖R₃₂R₂₁T₁ − T₃R₃₂R₂₁‖ ≤ ‖R₃₂‖ ‖R₂₁T₁ − T₂R₂₁‖ + ‖R₃₂T₂ − T₃R₃₂‖ ‖R₂₁‖`.

## 4. Fixed points / scale invariance
* `intertwiner_maps_eigenvector`, `intertwiner_maps_fixedPoint` (any intertwiner `R T = T' R`);
* `eigenspace_map_of_commute`, `fixedPoints_image_of_commute`: an invertible `R` commuting with
  `T` maps every eigenspace (resp. the fixed-point set) of `T` *onto* itself.

## 5. No-go: consistency does not determine the state space
* `consistent_of_trivial_dynamics`: `U = id` is consistent with every `R` between any finite sets;
* `consistent_total_mass`: every column-stochastic dynamics on any finite set is exactly
  consistent with the one-point model via the total-mass map;
* explicit models `T₃ = diag(1,2,3)` on `Fin 3`, `T₂ = diag(1,2)` on `Fin 2`, both consistent
  (`R₃₂_consistent`), with different spectra (`T₃_has_eigenvalue_three`,
  `T₂_no_eigenvalue_three`), and no injective consistent map between them
  (`consistent_map_kills_eigenvector`);
* `consistency_does_not_determine_state_space`: the packaged no-go statement.

## 6. Lumpability (Kemeny–Snell)
* `exists_intertwining_iff_isLumpable`: for any partition `π : S → B`, `∃ T', T V = V T'` iff `T`
  is lumpable (`V` = collection matrix); `lumped_rowStochastic`;
* `aggregation_consistent_iff_isLumpable`: the same as a consistency equation
  `R Tᵀ = T'ᵀ R` with the block-*summing* map `R = Vᵀ` on probability vectors;
  `pairBlock` gives the partition `Fin (2n) → Fin n`.
-/

open NormedSpace Matrix

namespace APEX.Unified


section Abstract
variable {𝔸 𝔹 V : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
  [NormedRing 𝔹] [NormedAlgebra ℝ 𝔹] [CompleteSpace 𝔹]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem map_exp_eq_of_pow (Lₗ : 𝔸 →L[ℝ] V) (Lᵣ : 𝔹 →L[ℝ] V) (a : 𝔸) (b : 𝔹)
    (h : ∀ n : ℕ, Lₗ (a ^ n) = Lᵣ (b ^ n)) : Lₗ (exp a) = Lᵣ (exp b) := by
  have ha := Lₗ.hasSum (exp_series_hasSum_exp' (𝕂 := ℝ) a)
  have hb := Lᵣ.hasSum (exp_series_hasSum_exp' (𝕂 := ℝ) b)
  simp only [map_smul, h] at ha hb
  exact ha.unique hb

theorem eq_of_map_exp_smul (Lₗ : 𝔸 →L[ℝ] V) (Lᵣ : 𝔹 →L[ℝ] V) (a : 𝔸) (b : 𝔹)
    (h : ∀ t : ℝ, Lₗ (exp (t • a)) = Lᵣ (exp (t • b))) : Lₗ a = Lᵣ b := by
  have d1 := HasFDerivAt.comp_hasDerivAt (0:ℝ) Lₗ.hasFDerivAt (hasDerivAt_exp_smul_const a (0:ℝ))
  have d2 := HasFDerivAt.comp_hasDerivAt (0:ℝ) Lᵣ.hasFDerivAt (hasDerivAt_exp_smul_const b (0:ℝ))
  have hf : (Lₗ ∘ fun u : ℝ => exp (u • a)) = (Lᵣ ∘ fun u : ℝ => exp (u • b)) := by
    funext u; exact h u
  rw [hf] at d1
  have := d1.unique d2
  simpa [zero_smul, exp_zero, one_mul] using this

end Abstract

section Operator
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem comp_pow_of_comp {R : E →L[ℝ] F} {T : E →L[ℝ] E} {T' : F →L[ℝ] F}
    (h : R.comp T = T'.comp R) (k : ℕ) : R.comp (T ^ k) = (T' ^ k).comp R := by
  induction k with
  | zero => simp [ContinuousLinearMap.one_def]
  | succ k ih =>
    rw [pow_succ, pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.comp_assoc, ih, ContinuousLinearMap.comp_assoc, h,
      ← ContinuousLinearMap.comp_assoc]

theorem comp_exp_iff (R : E →L[ℝ] F) (A : E →L[ℝ] E) (A' : F →L[ℝ] F) :
    (∀ t : ℝ, R.comp (exp (t • A)) = (exp (t • A')).comp R) ↔ R.comp A = A'.comp R := by
  let Lₗ : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] F) := ContinuousLinearMap.compL ℝ E E F R
  let Lᵣ : (F →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) := (ContinuousLinearMap.compL ℝ E F F).flip R
  have hl : ∀ X, Lₗ X = R.comp X := fun X => rfl
  have hr : ∀ X, Lᵣ X = X.comp R := fun X => rfl
  constructor
  · intro h
    have := eq_of_map_exp_smul Lₗ Lᵣ A A' (fun t => by rw [hl, hr]; exact h t)
    rwa [hl, hr] at this
  · intro h t
    have ht : R.comp (t • A) = (t • A').comp R := by
      rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, h]
    have := map_exp_eq_of_pow Lₗ Lᵣ (t • A) (t • A') (fun n => by
      rw [hl, hr]; exact comp_pow_of_comp ht n)
    rwa [hl, hr] at this

end Operator

section MatrixExp
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem mul_pow_of_mul {α : Type*} [Semiring α] {R : Matrix m n α} {T : Matrix n n α}
    {T' : Matrix m m α} (h : R * T = T' * R) (k : ℕ) : R * T ^ k = T' ^ k * R := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h,
      ← Matrix.mul_assoc]

theorem mul_pow_iff {α : Type*} [Semiring α] {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (R : Matrix m n α) (T : Matrix n n α) (T' : Matrix m m α) :
    (∀ k : ℕ, R * T ^ k = T' ^ k * R) ↔ R * T = T' * R :=
  ⟨fun h => by simpa using h 1, fun h k => mul_pow_of_mul h k⟩

theorem matrix_mul_exp_iff (R : Matrix m n ℝ) (A : Matrix n n ℝ) (A' : Matrix m m ℝ) :
    (∀ t : ℝ, R * exp (t • A) = exp (t • A') * R) ↔ R * A = A' * R := by
  let : NormedAddCommGroup (Matrix m n ℝ) := Matrix.linftyOpNormedAddCommGroup
  let : NormedSpace ℝ (Matrix m n ℝ) := Matrix.linftyOpNormedSpace
  let : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra
  let : NormedRing (Matrix m m ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix m m ℝ) := Matrix.linftyOpNormedAlgebra
  let Lₗ : Matrix n n ℝ →L[ℝ] Matrix m n ℝ :=
    LinearMap.mkContinuous
      { toFun := fun X => R * X, map_add' := Matrix.mul_add R,
        map_smul' := fun c X => Matrix.mul_smul R c X } ‖R‖
      (fun X => Matrix.linfty_opNorm_mul R X)
  let Lᵣ : Matrix m m ℝ →L[ℝ] Matrix m n ℝ :=
    LinearMap.mkContinuous
      { toFun := fun X => X * R, map_add' := fun X Y => Matrix.add_mul X Y R,
        map_smul' := fun c X => Matrix.smul_mul c X R } ‖R‖
      (fun X => by rw [mul_comm]; exact Matrix.linfty_opNorm_mul X R)
  constructor
  · intro h
    exact eq_of_map_exp_smul Lₗ Lᵣ A A' h
  · intro h t
    have ht : R * (t • A) = (t • A') * R := by
      rw [Matrix.mul_smul, Matrix.smul_mul, h]
    exact map_exp_eq_of_pow Lₗ Lᵣ (t • A) (t • A') (fun k => mul_pow_of_mul ht k)

end MatrixExp

section Defect
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The one-step (generator) defect `D = R T − T' R`. -/
def defect (R : E →L[ℝ] F) (T : E →L[ℝ] E) (T' : F →L[ℝ] F) : E →L[ℝ] F :=
  R.comp T - T'.comp R

theorem opNorm_pow_le (T : E →L[ℝ] E) (k : ℕ) : ‖T ^ k‖ ≤ ‖T‖ ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [ContinuousLinearMap.one_def] using ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' T hk

theorem defect_pow_succ (R : E →L[ℝ] F) (T : E →L[ℝ] E) (T' : F →L[ℝ] F) (k : ℕ) :
    R.comp (T ^ (k + 1)) - (T' ^ (k + 1)).comp R =
      T'.comp (R.comp (T ^ k) - (T' ^ k).comp R) + (defect R T T').comp (T ^ k) := by
  rw [pow_succ', pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, defect,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  simp only [ContinuousLinearMap.comp_assoc]
  abel

/-- Discrete Duhamel bound. -/
theorem norm_defect_pow_le (R : E →L[ℝ] F) (T : E →L[ℝ] E) (T' : F →L[ℝ] F) (k : ℕ) :
    ‖R.comp (T ^ k) - (T' ^ k).comp R‖ ≤
      ∑ j ∈ Finset.range k, ‖T'‖ ^ (k - 1 - j) * ‖defect R T T'‖ * ‖T‖ ^ j := by
  induction k with
  | zero => simp [ContinuousLinearMap.one_def]
  | succ k ih =>
    rw [defect_pow_succ, Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero,
      one_mul]
    have h1 : ∑ j ∈ Finset.range k, ‖T'‖ ^ (k - j) * ‖defect R T T'‖ * ‖T‖ ^ j =
        ‖T'‖ * ∑ j ∈ Finset.range k, ‖T'‖ ^ (k - 1 - j) * ‖defect R T T'‖ * ‖T‖ ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : k - j = (k - 1 - j) + 1 := by
        have := Finset.mem_range.1 hj; omega
      rw [hj', pow_succ]; ring
    rw [h1]
    calc ‖T'.comp (R.comp (T ^ k) - (T' ^ k).comp R) + (defect R T T').comp (T ^ k)‖
        ≤ ‖T'.comp (R.comp (T ^ k) - (T' ^ k).comp R)‖ + ‖(defect R T T').comp (T ^ k)‖ :=
          norm_add_le _ _
      _ ≤ ‖T'‖ * ‖R.comp (T ^ k) - (T' ^ k).comp R‖ + ‖defect R T T'‖ * ‖T ^ k‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ _ := by
          gcongr
          exact opNorm_pow_le T k

/-- For contractions the defect grows at most linearly. -/
theorem norm_defect_pow_le_of_contraction (R : E →L[ℝ] F) (T : E →L[ℝ] E) (T' : F →L[ℝ] F)
    (hT : ‖T‖ ≤ 1) (hT' : ‖T'‖ ≤ 1) (k : ℕ) :
    ‖R.comp (T ^ k) - (T' ^ k).comp R‖ ≤ k * ‖defect R T T'‖ := by
  refine (norm_defect_pow_le R T T' k).trans ?_
  calc ∑ j ∈ Finset.range k, ‖T'‖ ^ (k - 1 - j) * ‖defect R T T'‖ * ‖T‖ ^ j
      ≤ ∑ _j ∈ Finset.range k, ‖defect R T T'‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        have a := pow_le_one₀ (norm_nonneg T') hT' (n := k - 1 - j)
        have b := pow_le_one₀ (norm_nonneg T) hT (n := j)
        have c := norm_nonneg (defect R T T')
        calc ‖T'‖ ^ (k - 1 - j) * ‖defect R T T'‖ * ‖T‖ ^ j
            ≤ 1 * ‖defect R T T'‖ * 1 := by gcongr
          _ = _ := by ring
    _ = k * ‖defect R T T'‖ := by simp

/-- ... and is uniformly bounded by `2‖R‖`, so linear growth saturates. -/
theorem norm_defect_pow_le_two_mul (R : E →L[ℝ] F) (T : E →L[ℝ] E) (T' : F →L[ℝ] F)
    (hT : ‖T‖ ≤ 1) (hT' : ‖T'‖ ≤ 1) (k : ℕ) :
    ‖R.comp (T ^ k) - (T' ^ k).comp R‖ ≤ 2 * ‖R‖ := by
  have a : ‖T ^ k‖ ≤ 1 := (opNorm_pow_le T k).trans (pow_le_one₀ (norm_nonneg _) hT)
  have b : ‖T' ^ k‖ ≤ 1 := (opNorm_pow_le T' k).trans (pow_le_one₀ (norm_nonneg _) hT')
  have hR := norm_nonneg R
  calc ‖R.comp (T ^ k) - (T' ^ k).comp R‖ ≤ ‖R.comp (T ^ k)‖ + ‖(T' ^ k).comp R‖ :=
        norm_sub_le _ _
    _ ≤ ‖R‖ * ‖T ^ k‖ + ‖T' ^ k‖ * ‖R‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖R‖ * 1 + 1 * ‖R‖ := by gcongr
    _ = 2 * ‖R‖ := by ring

end Defect

section Compose
variable {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]

theorem norm_defect_comp_le (R₂₁ : E₁ →L[ℝ] E₂) (R₃₂ : E₂ →L[ℝ] E₃) (T₁ : E₁ →L[ℝ] E₁)
    (T₂ : E₂ →L[ℝ] E₂) (T₃ : E₃ →L[ℝ] E₃) :
    ‖defect (R₃₂.comp R₂₁) T₁ T₃‖ ≤
      ‖R₃₂‖ * ‖defect R₂₁ T₁ T₂‖ + ‖defect R₃₂ T₂ T₃‖ * ‖R₂₁‖ := by
  have e : defect (R₃₂.comp R₂₁) T₁ T₃ =
      R₃₂.comp (defect R₂₁ T₁ T₂) + (defect R₃₂ T₂ T₃).comp R₂₁ := by
    simp only [defect, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_assoc]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _))

end Compose

/-- In any ring, `[R,S] = S` forces `[R,S^k] = k S^k`: exact linear growth of the defect. -/
theorem commutator_pow_of_commutator_eq_self {α : Type*} [Ring α] (R S : α)
    (h : R * S - S * R = S) (k : ℕ) : R * S ^ k - S ^ k * R = (k : α) * S ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : R * S ^ (k + 1) - S ^ (k + 1) * R =
        (R * S ^ k - S ^ k * R) * S + S ^ k * (R * S - S * R) := by
      rw [pow_succ]; simp only [sub_mul, mul_sub, mul_assoc]; abel
    rw [e, ih, h, pow_succ]; push_cast; rw [add_mul, one_mul, mul_assoc]

section ShiftExample
variable (N : ℕ)

/-- The shift `(S v)_i = v_{i-1}` (and `(S v)_0 = 0`) on `Fin N → ℝ` with the sup norm. -/
noncomputable def shiftOp : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun v i => if h : 1 ≤ (i : ℕ) then v ⟨(i : ℕ) - 1, by omega⟩ else 0
      map_add' := fun v w => by funext i; by_cases h : 1 ≤ (i : ℕ) <;> simp [h]
      map_smul' := fun c v => by funext i; by_cases h : 1 ≤ (i : ℕ) <;> simp [h] } 1
    (fun v => by
      rw [one_mul]
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun i => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      split_ifs
      · exact norm_le_pi_norm v _
      · simp)

/-- The position operator `(X v)_i = i · v_i`. -/
noncomputable def posOp : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun v i => ((i : ℕ) : ℝ) * v i
      map_add' := fun v w => by funext i; simp [mul_add]
      map_smul' := fun c v => by funext i; simp; ring } N
    (fun v => by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_mul, Real.norm_natCast]
      gcongr
      · exact_mod_cast i.isLt.le
      · exact norm_le_pi_norm v _)

theorem shiftOp_apply (v : Fin N → ℝ) (i : Fin N) :
    shiftOp N v i = if h : 1 ≤ (i : ℕ) then v ⟨(i : ℕ) - 1, by omega⟩ else 0 := rfl

theorem posOp_apply (v : Fin N → ℝ) (i : Fin N) : posOp N v i = ((i : ℕ) : ℝ) * v i := rfl

theorem shiftOp_pow_apply (k : ℕ) (v : Fin N → ℝ) (i : Fin N) :
    (shiftOp N ^ k) v i = if h : k ≤ (i : ℕ) then v ⟨(i : ℕ) - k, by omega⟩ else 0 := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, shiftOp_apply]
    by_cases h1 : 1 ≤ (i : ℕ)
    · rw [dite_eq_left h1, ih]
      by_cases h2 : k + 1 ≤ (i : ℕ)
      · rw [dite_eq_left (show k ≤ ((⟨(i : ℕ) - 1, by omega⟩ : Fin N) : ℕ) by simp; omega),
          dite_eq_left h2]
        congr 1; ext; simp; omega
      · rw [dite_eq_right (show ¬ k ≤ ((⟨(i : ℕ) - 1, by omega⟩ : Fin N) : ℕ) by simp; omega),
          dite_eq_right h2]
    · rw [dite_eq_right h1, dite_eq_right (by omega)]

theorem posOp_shiftOp_commutator : posOp N * shiftOp N - shiftOp N * posOp N = shiftOp N := by
  ext v i
  simp only [sub_apply, mul_apply_eq_comp, Pi.sub_apply]
  by_cases h : 1 ≤ (i : ℕ)
  · have : (((⟨(i : ℕ) - 1, by omega⟩ : Fin N) : ℕ) : ℝ) = ((i : ℕ) : ℝ) - 1 := by
      simp only; rw [Nat.cast_sub h]; simp
    simp only [posOp_apply, shiftOp_apply, dite_eq_left h]
    rw [this]; ring
  · simp only [posOp_apply, shiftOp_apply, dite_eq_right h]; ring

theorem norm_shiftOp_le : ‖shiftOp N‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem one_le_norm_shiftOp_pow {k : ℕ} (hk : k < N) : 1 ≤ ‖shiftOp N ^ k‖ := by
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have h1 := (shiftOp N ^ k).le_opNorm (fun _ => (1 : ℝ))
  have hc : ‖(fun _ : Fin N => (1 : ℝ))‖ = 1 := by simp
  rw [hc, mul_one] at h1
  have h2 := norm_le_pi_norm ((shiftOp N ^ k) (fun _ => (1 : ℝ))) ⟨N - 1, by omega⟩
  rw [shiftOp_pow_apply, dite_eq_left (by simp; omega)] at h2
  simp at h2
  linarith

theorem norm_shiftOp_pow {k : ℕ} (hk : k < N) : ‖shiftOp N ^ k‖ = 1 := by
  refine le_antisymm ?_ (one_le_norm_shiftOp_pow N hk)
  calc ‖shiftOp N ^ k‖ ≤ ‖shiftOp N‖ ^ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simpa [ContinuousLinearMap.one_def] using ContinuousLinearMap.norm_id_le
        · exact norm_pow_le' _ hk0
    _ ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_shiftOp_le N)

/-- Sharpness: `T = T' = S` is a contraction, the one-step defect of `R = X` has norm `1`,
and the `k`-step defect has norm exactly `k` for every `k < N`. -/
theorem shift_defect_grows_linearly (hN : 2 ≤ N) :
    ‖shiftOp N‖ ≤ 1 ∧
    ‖posOp N * shiftOp N - shiftOp N * posOp N‖ = 1 ∧
    ∀ k : ℕ, k < N → ‖posOp N * shiftOp N ^ k - shiftOp N ^ k * posOp N‖ =
      k * ‖posOp N * shiftOp N - shiftOp N * posOp N‖ := by
  have hD := posOp_shiftOp_commutator N
  have hS1 : ‖shiftOp N‖ = 1 := by simpa using norm_shiftOp_pow N (k := 1) (by omega)
  refine ⟨norm_shiftOp_le N, by rw [hD, hS1], fun k hk => ?_⟩
  rw [commutator_pow_of_commutator_eq_self _ _ hD k, hD, hS1, ← nsmul_eq_mul,
    ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, norm_shiftOp_pow N hk]
  simp

end ShiftExample

section FixedPoints
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem intertwiner_maps_eigenvector {R : V →ₗ[K] W} {T : Module.End K V} {T' : Module.End K W}
    (h : R ∘ₗ T = T' ∘ₗ R) {μ : K} {v : V} (hv : T v = μ • v) : T' (R v) = μ • R v := by
  have := LinearMap.congr_fun h v
  simp only [LinearMap.comp_apply] at this
  rw [← this, hv, map_smul]

theorem intertwiner_maps_fixedPoint {R : V →ₗ[K] W} {T : Module.End K V} {T' : Module.End K W}
    (h : R ∘ₗ T = T' ∘ₗ R) {v : V} (hv : T v = v) : T' (R v) = R v := by
  simpa using intertwiner_maps_eigenvector (μ := (1 : K)) h (by simpa using hv)

theorem eigenspace_map_of_commute (R : V ≃ₗ[K] V) (T : Module.End K V)
    (h : (R : Module.End K V) ∘ₗ T = T ∘ₗ (R : Module.End K V)) (μ : K) :
    (Module.End.eigenspace T μ).map (R : Module.End K V) = Module.End.eigenspace T μ := by
  have hR : ∀ v, R (T v) = T (R v) := fun v => LinearMap.congr_fun h v
  have hRinv : ∀ v, R.symm (T v) = T (R.symm v) := fun v => by
    have := hR (R.symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, LinearEquiv.symm_apply_apply]
  ext v
  simp only [Submodule.mem_map, Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact intertwiner_maps_eigenvector h hw
  · intro hv
    refine ⟨R.symm v, ?_, by simp⟩
    rw [← hRinv, hv, map_smul]

theorem fixedPoints_image_of_commute (R : V ≃ₗ[K] V) (T : Module.End K V)
    (h : (R : Module.End K V) ∘ₗ T = T ∘ₗ (R : Module.End K V)) :
    R '' {v | T v = v} = {v | T v = v} := by
  have := eigenspace_map_of_commute R T h 1
  ext v
  have hv := congrArg (fun S : Submodule K V => v ∈ S) this
  simp only [Submodule.mem_map, Module.End.mem_eigenspace_iff, one_smul, eq_iff_iff] at hv
  simpa using hv

end FixedPoints

/-- Abstract consistency: `R ∘ U(t) = U'(t) ∘ R` for every time `t`. -/
def Consistent {τ α m n : Type*} [Fintype m] [Fintype n] [Semiring α]
    (R : Matrix m n α) (U : τ → Matrix n n α) (U' : τ → Matrix m m α) : Prop :=
  ∀ t, R * U t = U' t * R

section Compose
variable {τ α : Type*} [Semiring α] {n₁ n₂ n₃ : Type*} [Fintype n₁] [Fintype n₂] [Fintype n₃]

theorem Consistent.comp {R₂₁ : Matrix n₂ n₁ α} {R₃₂ : Matrix n₃ n₂ α}
    {U₁ : τ → Matrix n₁ n₁ α} {U₂ : τ → Matrix n₂ n₂ α} {U₃ : τ → Matrix n₃ n₃ α}
    (h₂₁ : Consistent R₂₁ U₁ U₂) (h₃₂ : Consistent R₃₂ U₂ U₃) :
    Consistent (R₃₂ * R₂₁) U₁ U₃ := fun t => by
  rw [Matrix.mul_assoc, h₂₁ t, ← Matrix.mul_assoc, h₃₂ t, Matrix.mul_assoc]

theorem consistent_one [DecidableEq n₁] (U : τ → Matrix n₁ n₁ α) :
    Consistent (1 : Matrix n₁ n₁ α) U U := fun t => by simp

end Compose

section NoGo
variable {α : Type*} [CommSemiring α]

/-- Trivial dynamics is consistent with every coarse-graining map. -/
theorem consistent_of_trivial_dynamics {τ m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (R : Matrix m n α) :
    Consistent R (fun _ : τ => (1 : Matrix n n α)) (fun _ => 1) := fun t => by simp

/-- Any column-stochastic dynamics on any finite state space is exactly consistent with the
one-point coarse model, via the total-mass map `R = (1 … 1)`. -/
theorem consistent_total_mass {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n α)
    (hT : ∀ j, ∑ i, T i j = 1) (k : ℕ) :
    (Matrix.of fun (_ : Fin 1) (_ : n) => (1 : α)) * T ^ k =
      (1 : Matrix (Fin 1) (Fin 1) α) ^ k * Matrix.of fun (_ : Fin 1) (_ : n) => (1 : α) := by
  have h1 : (Matrix.of fun (_ : Fin 1) (_ : n) => (1 : α)) * T =
      (1 : Matrix (Fin 1) (Fin 1) α) * Matrix.of fun (_ : Fin 1) (_ : n) => (1 : α) := by
    rw [Matrix.one_mul]; ext a j; simp [Matrix.mul_apply, hT j]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← Matrix.mul_assoc, h1, Matrix.mul_assoc, ih, one_pow, one_pow,
      Matrix.one_mul, Matrix.one_mul]

end NoGo

section Examples

/-- Fine model on `Fin 3`: `T₃ = diag(1,2,3)`. -/
def T₃ : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 2, 3]
/-- Coarse model on `Fin 2`: `T₂ = diag(1,2)`. -/
def T₂ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 2]
/-- Coarse-graining `Fin 3 → Fin 2`: forget the last coordinate. -/
def R₃₂ : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0]

theorem R₃₂_consistent : R₃₂ * T₃ = T₂ * R₃₂ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [R₃₂, T₃, T₂, Matrix.mul_apply, Matrix.diagonal]

theorem T₃_has_eigenvalue_three : T₃ *ᵥ Pi.single 2 1 = (3 : ℝ) • Pi.single 2 1 := by
  ext i; fin_cases i <;> simp [T₃, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem T₂_no_eigenvalue_three (v : Fin 2 → ℝ) (hv : T₂ *ᵥ v = (3 : ℝ) • v) : v = 0 := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [T₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  ext i; fin_cases i <;> simp <;> linarith

end Examples

section NoGoPackaged

/-- An injective-on-eigenvector obstruction: any consistent map `P : Fin 3 → Fin 2` from the
`T₃` model to the `T₂` model kills the eigenvalue-3 eigenvector; in particular no consistent
map between the two models is injective (they are not isomorphic). -/
theorem consistent_map_kills_eigenvector (P : Matrix (Fin 2) (Fin 3) ℝ)
    (hP : P * T₃ = T₂ * P) : P *ᵥ Pi.single 2 1 = 0 := by
  apply T₂_no_eigenvalue_three
  rw [Matrix.mulVec_mulVec, ← hP, ← Matrix.mulVec_mulVec, T₃_has_eigenvalue_three,
    Matrix.mulVec_smul]

/-- **No-go theorem.** The consistency equation alone does not determine the state space:
(i) for every pair of finite dimensions `n, m` and *every* linear `R`, the trivial continuous-time
dynamics `exp(t·0) = 1` is exactly consistent; (ii) two models with different state spaces and
different spectra (`Fin 3`, spectrum containing `3`; `Fin 2`, spectrum not containing `3`) are
both exactly consistent in continuous time, linked by a coarse-graining; and (iii) no consistent
map between them is injective, so they are not isomorphic. -/
theorem consistency_does_not_determine_state_space :
    (∀ (n m : ℕ) (R : Matrix (Fin m) (Fin n) ℝ) (t : ℝ),
      R * exp (t • (0 : Matrix (Fin n) (Fin n) ℝ)) =
        exp (t • (0 : Matrix (Fin m) (Fin m) ℝ)) * R) ∧
    (∀ t : ℝ, R₃₂ * exp (t • T₃) = exp (t • T₂) * R₃₂) ∧
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ T₃ *ᵥ v = (3 : ℝ) • v) ∧
    (∀ v : Fin 2 → ℝ, T₂ *ᵥ v = (3 : ℝ) • v → v = 0) ∧
    (∀ P : Matrix (Fin 2) (Fin 3) ℝ, P * T₃ = T₂ * P → ¬ Function.Injective P.mulVec) := by
  refine ⟨fun n m R t => ?_, (matrix_mul_exp_iff R₃₂ T₃ T₂).2 R₃₂_consistent,
    ⟨Pi.single 2 1, fun h => by simpa using congrFun h 2, T₃_has_eigenvalue_three⟩,
    T₂_no_eigenvalue_three, fun P hP hinj => ?_⟩
  · rw [smul_zero, smul_zero, NormedSpace.exp_zero, NormedSpace.exp_zero, Matrix.mul_one,
      Matrix.one_mul]
  · have h := consistent_map_kills_eigenvector P hP
    have : Pi.single (2 : Fin 3) (1 : ℝ) = 0 := hinj (by rw [h, Matrix.mulVec_zero])
    simpa using congrFun this 2

end NoGoPackaged

section Lumpability
variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]

/-- Collection matrix `V_{i b} = [π i = b]` of a partition `π : S → B`. -/
def collect (π : S → B) : Matrix S B ℝ := Matrix.of fun i b => if π i = b then 1 else 0

/-- Kemeny–Snell lumpability: the probability of jumping into block `b` depends only on the
block of the starting state. -/
def IsLumpable (T : Matrix S S ℝ) (π : S → B) : Prop :=
  ∀ i i', π i = π i' → ∀ b, ∑ j ∈ Finset.univ.filter (fun j => π j = b), T i j =
    ∑ j ∈ Finset.univ.filter (fun j => π j = b), T i' j

omit [Fintype B] in
theorem mul_collect_apply (T : Matrix S S ℝ) (π : S → B) (i : S) (b : B) :
    (T * collect π) i b = ∑ j ∈ Finset.univ.filter (fun j => π j = b), T i j := by
  simp [collect, Matrix.mul_apply, Finset.sum_filter]

omit [Fintype S] in
theorem collect_mul_apply (π : S → B) (T' : Matrix B B ℝ) (i : S) (b : B) :
    (collect π * T') i b = T' (π i) b := by
  simp [collect, Matrix.mul_apply]

/-- Lumpability ⟺ existence of a coarse matrix `T'` with `T V = V T'`. -/
theorem exists_intertwining_iff_isLumpable (T : Matrix S S ℝ) (π : S → B) :
    (∃ T' : Matrix B B ℝ, T * collect π = collect π * T') ↔ IsLumpable T π := by
  constructor
  · rintro ⟨T', hT'⟩ i i' hii' b
    have h1 := congrFun (congrFun hT' i) b
    have h2 := congrFun (congrFun hT' i') b
    rw [mul_collect_apply, collect_mul_apply] at h1 h2
    rw [h1, h2, hii']
  · intro h
    classical
    refine ⟨Matrix.of fun c b => if hc : ∃ i, π i = c then
      ∑ j ∈ Finset.univ.filter (fun j => π j = b), T hc.choose j else 0, ?_⟩
    ext i b
    rw [mul_collect_apply, collect_mul_apply]
    have hc : ∃ i', π i' = π i := ⟨i, rfl⟩
    simp only [Matrix.of_apply, dite_eq_left hc]
    exact h _ _ hc.choose_spec.symm b

/-- The lumped matrix of a row-stochastic lumpable chain is row-stochastic. -/
theorem lumped_rowStochastic (T : Matrix S S ℝ) (π : S → B) (T' : Matrix B B ℝ)
    (hT : ∀ i, ∑ j, T i j = 1) (hπ : Function.Surjective π)
    (h : T * collect π = collect π * T') : ∀ c, ∑ b, T' c b = 1 := by
  intro c
  obtain ⟨i, rfl⟩ := hπ c
  have : ∀ b, T' (π i) b = ∑ j ∈ Finset.univ.filter (fun j => π j = b), T i j := fun b => by
    rw [← collect_mul_apply π T' i b, ← h, mul_collect_apply]
  simp only [this]
  rw [Finset.sum_fiberwise]
  exact hT i

/-- Consistency form: with the aggregation matrix `R = Vᵀ` (sum over each block) acting on
probability column vectors, which evolve by `Tᵀ`, the consistency equation
`R Tᵀ = T'ᵀ R` holds for some coarse `T'` iff `T` is lumpable. -/
theorem aggregation_consistent_iff_isLumpable (T : Matrix S S ℝ) (π : S → B) :
    (∃ T' : Matrix B B ℝ, (collect π)ᵀ * Tᵀ = T'ᵀ * (collect π)ᵀ) ↔ IsLumpable T π := by
  rw [← exists_intertwining_iff_isLumpable]
  refine exists_congr fun T' => ?_
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul]
  exact Matrix.transpose_inj

/-- Pairing partition `Fin (2n) → Fin n`, `i ↦ ⌊i/2⌋`. -/
def pairBlock (n : ℕ) : Fin (2 * n) → Fin n := fun i => ⟨(i : ℕ) / 2, by omega⟩

theorem pairBlock_surjective (n : ℕ) : Function.Surjective (pairBlock n) := fun b =>
  ⟨⟨2 * b, by omega⟩, by ext; simp [pairBlock]⟩

end Lumpability
end APEX.Unified

