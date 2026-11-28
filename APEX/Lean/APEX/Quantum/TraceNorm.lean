import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Matrix Polynomial
open scoped ComplexOrder

set_option linter.unusedSectionVars false

/-!
# Trace norm of complex matrices

Mathlib (v4.36 snapshot) has the spectral theorem for Hermitian matrices
(`Matrix.IsHermitian.eigenvalues`, `eigenvectorUnitary`, `spectral_theorem`, `charpoly_eq`),
PSD matrices and CFC on matrices, but **no Schatten/trace norm**. We define, for
`A : Matrix n n ℂ`,

  `traceNorm A = Σ_i √(λ_i(Aᴴ A))`   (sum of singular values = `tr √(AᴴA)`),

and prove:
* `traceNorm_eq_sum_abs`: for Hermitian `A`, `‖A‖₁ = Σ_i |λ_i(A)|`.
* `traceNorm_nonneg`, `traceNorm_eq_zero_iff` (`‖A‖₁ = 0 ↔ A = 0`, any square `A`).
* `traceNorm_unitary_conj`: `‖U A U*‖₁ = ‖A‖₁` (any square `A`); `traceNorm_neg`.
* `traceNorm_of_posSemidef`: `‖M‖₁ = Re tr M` for `M ≥ 0`; `traceNorm_density`: `‖ρ‖₁ = 1`.
* `norm_trace_mul_le`: `|tr(Q A)| ≤ ‖A‖₁` for Hermitian `A` and `0 ≤ Q`, `0 ≤ 1 − Q`.
* `helstrom_le`, `traceNorm_isGreatest` (**Helstrom / variational formula**): for Hermitian `A`,
  `‖A‖₁ = max_{P projector} Re[tr(P A) − tr((1−P) A)]`, attained at the positive spectral
  projector `posProj`.
* `traceNorm_add_le`, `traceNorm_sub_le`, `traceNorm_sum_le`: triangle inequality (Hermitian
  arguments).
* `traceNorm_ketbra_sub_orthogonal`: for orthonormal `ψ, φ`, `‖|ψ⟩⟨ψ| − |φ⟩⟨φ|‖₁ = 2`.

Not done: the triangle inequality / Hölder duality for non-Hermitian matrices, and
contractivity of `‖·‖₁` under CPTP maps.
-/

namespace APEX.Quantum

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def traceNorm (A : Matrix n n ℂ) : ℝ :=
  ∑ i, Real.sqrt ((isHermitian_conjTranspose_mul_self A).eigenvalues i)

lemma charpoly_unitary_conj (U : unitaryGroup n ℂ) (M : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * M * star (U : Matrix n n ℂ)).charpoly = M.charpoly := by
  rw [charpoly_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

lemma sum_eq_of_roots {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) (g : ℝ → ℝ) :
    ∑ i, g (hA.eigenvalues i) = ∑ i, g (hB.eigenvalues i) := by
  rw [(hA.eigenvalues_eq_eigenvalues_iff hB).2 h]

lemma charpoly_sq_herm {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Aᴴ * A).charpoly = ∏ i, (X - C (((hA.eigenvalues i) ^ 2 : ℝ) : ℂ)) := by
  have hsq : Aᴴ * A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => (((hA.eigenvalues i) ^ 2 : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
    rw [hA.eq]
    conv_lhs => rw [hA.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    have hu := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rw [show ∀ (P Q R S T : Matrix n n ℂ), P * Q * R * (S * T * R) = P * Q * (R * S) * T * R by
      intro P Q R S T; simp only [Matrix.mul_assoc]]
    rw [hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext i; simp [pow_two]
  rw [hsq, charpoly_unitary_conj, charpoly_diagonal]

omit [DecidableEq n] in
lemma roots_prod_fintype (f : n → ℂ) :
    (∏ i, (X - C (f i))).roots = Multiset.map f Finset.univ.val := by
  rw [Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

theorem traceNorm_eq_sum_abs {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm A = ∑ i, |hA.eigenvalues i| := by
  have hB := isHermitian_conjTranspose_mul_self A
  have h1 := hB.roots_charpoly_eq_eigenvalues
  rw [charpoly_sq_herm hA, roots_prod_fintype] at h1
  have h2 := congrArg (fun s => (Multiset.map (fun z : ℂ => Real.sqrt z.re) s).sum) h1
  simp only [Multiset.map_map] at h2
  unfold traceNorm
  have e1 : ∑ i, |hA.eigenvalues i| = ∑ i, Real.sqrt ((hA.eigenvalues i) ^ 2) := by
    simp [Real.sqrt_sq_eq_abs]
  rw [e1]
  simpa [Finset.sum_map_val, Function.comp_def, ← Complex.ofReal_pow, Complex.ofReal_re] using h2.symm

/-! ### Basic properties -/

theorem traceNorm_nonneg (A : Matrix n n ℂ) : 0 ≤ traceNorm A :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

lemma traceNorm_congr {A B : Matrix n n ℂ} (h : (Aᴴ * A).charpoly = (Bᴴ * B).charpoly) :
    traceNorm A = traceNorm B := by
  unfold traceNorm
  rw [((isHermitian_conjTranspose_mul_self A).eigenvalues_eq_eigenvalues_iff
    (isHermitian_conjTranspose_mul_self B)).2 h]

theorem traceNorm_eq_zero_iff (A : Matrix n n ℂ) : traceNorm A = 0 ↔ A = 0 := by
  have hB := isHermitian_conjTranspose_mul_self A
  constructor
  · intro h
    have h0 : ∀ i, Real.sqrt (hB.eigenvalues i) = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Real.sqrt_nonneg _)).1 h i
        (Finset.mem_univ _)
    have he : hB.eigenvalues = 0 := by
      funext i
      have h1 := Real.sqrt_eq_zero'.1 (h0 i)
      have h2 := eigenvalues_conjTranspose_mul_self_nonneg A i
      simp only [Pi.zero_apply]; linarith
    exact conjTranspose_mul_self_eq_zero.1 (hB.eigenvalues_eq_zero_iff.1 he)
  · intro h
    have he : hB.eigenvalues = 0 := hB.eigenvalues_eq_zero_iff.2 (by simp [h])
    unfold traceNorm
    simp [he]

/-- Unitary invariance (for arbitrary square `A`). -/
theorem traceNorm_unitary_conj (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    traceNorm ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)) = traceNorm A := by
  apply traceNorm_congr
  have : ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ))ᴴ *
      ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)) =
      (U : Matrix n n ℂ) * (Aᴴ * A) * star (U : Matrix n n ℂ) := by
    have hu := Unitary.coe_star_mul_self U
    simp only [← star_eq_conjTranspose, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U : Matrix n n ℂ)) (U : Matrix n n ℂ), hu, Matrix.one_mul]
  rw [this, charpoly_unitary_conj]

theorem traceNorm_neg (A : Matrix n n ℂ) : traceNorm (-A) = traceNorm A := by
  apply traceNorm_congr; simp

/-- For a positive semidefinite matrix the trace norm is the trace. -/
theorem traceNorm_of_posSemidef {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    traceNorm M = (trace M).re := by
  rw [traceNorm_eq_sum_abs hM.1, hM.1.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hM.eigenvalues_nonneg i)

/-- Density matrices have trace norm one. -/
theorem traceNorm_density {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    traceNorm ρ = 1 := by
  rw [traceNorm_of_posSemidef hρ, htr, Complex.one_re]

/-! ### Variational characterisation -/

/-- An orthogonal projector. -/
def IsProjector (P : Matrix n n ℂ) : Prop := Pᴴ = P ∧ P * P = P

lemma IsProjector.posSemidef {P : Matrix n n ℂ} (h : IsProjector P) : P.PosSemidef := by
  have : P = Pᴴ * P := by rw [h.1, h.2]
  rw [this]; exact posSemidef_conjTranspose_mul_self P

lemma IsProjector.one_sub {P : Matrix n n ℂ} (h : IsProjector P) : IsProjector (1 - P) := by
  refine ⟨by rw [conjTranspose_sub, conjTranspose_one, h.1], ?_⟩
  rw [sub_mul, mul_sub, mul_sub, h.2, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]; abel

lemma trace_mul_herm {A : Matrix n n ℂ} (hA : A.IsHermitian) (Q : Matrix n n ℂ) :
    trace (Q * A) = ∑ i, (star (hA.eigenvectorUnitary : Matrix n n ℂ) * Q *
      (hA.eigenvectorUnitary : Matrix n n ℂ)) i i * (hA.eigenvalues i : ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [show ∀ X Y Z W : Matrix n n ℂ, X * (Y * Z * W) = (X * Y * Z) * W by
    intro X Y Z W; simp only [Matrix.mul_assoc], trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]
  simp [trace, mul_diagonal]

lemma diag_bounds {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) (i : n) :
    Q i i = ((Q i i).re : ℂ) ∧ 0 ≤ (Q i i).re := by
  have h := hQ.diag_nonneg (i := i)
  rw [Complex.nonneg_iff] at h
  exact ⟨Complex.ext (by simp) (by simp [h.2.symm]), h.1⟩

/-- Helstrom bound: for Hermitian `A` and `0 ≤ Q`, `0 ≤ 1 - Q`,
`Re tr(Q A) - Re tr((1-Q) A) ≤ ‖A‖₁`. -/
theorem helstrom_le {A Q : Matrix n n ℂ} (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    (hQ1 : (1 - Q).PosSemidef) :
    (trace (Q * A) - trace ((1 - Q) * A)).re ≤ traceNorm A := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hu : star U * U = 1 := Unitary.coe_star_mul_self _
  have hW := hQ.conjTranspose_mul_mul_same U
  have hW' := hQ1.conjTranspose_mul_mul_same U
  rw [← star_eq_conjTranspose] at hW hW'
  have hsum : ∀ i, (star U * Q * U) i i + (star U * (1 - Q) * U) i i = 1 := by
    intro i
    rw [← Matrix.add_apply, ← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one,
      hu, one_apply_eq]
  rw [trace_mul_herm hA, trace_mul_herm hA, ← Finset.sum_sub_distrib, Complex.re_sum,
    traceNorm_eq_sum_abs hA]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨e1, p1⟩ := diag_bounds hW i
  obtain ⟨e2, p2⟩ := diag_bounds hW' i
  have hs := hsum i
  rw [e1, e2] at hs ⊢
  have hs' : ((star U * Q * U) i i).re + ((star U * (1 - Q) * U) i i).re = 1 := by
    have := congrArg Complex.re hs; simpa using this
  rw [← sub_mul, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
  set a := ((star U * Q * U) i i).re
  set b := ((star U * (1 - Q) * U) i i).re
  have hab : |a - b| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  calc (a - b) * hA.eigenvalues i ≤ |(a - b) * hA.eigenvalues i| := le_abs_self _
    _ = |a - b| * |hA.eigenvalues i| := abs_mul _ _
    _ ≤ 1 * |hA.eigenvalues i| := mul_le_mul_of_nonneg_right hab (abs_nonneg _)
    _ = |hA.eigenvalues i| := one_mul _

/-- `|tr(Q A)| ≤ ‖A‖₁` for Hermitian `A` and an effect `0 ≤ Q ≤ 1`. -/
theorem norm_trace_mul_le {A Q : Matrix n n ℂ} (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    (hQ1 : (1 - Q).PosSemidef) : ‖trace (Q * A)‖ ≤ traceNorm A := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hu : star U * U = 1 := Unitary.coe_star_mul_self _
  have hW := hQ.conjTranspose_mul_mul_same U
  have hW' := hQ1.conjTranspose_mul_mul_same U
  rw [← star_eq_conjTranspose] at hW hW'
  have hsum : ∀ i, (star U * Q * U) i i + (star U * (1 - Q) * U) i i = 1 := by
    intro i
    rw [← Matrix.add_apply, ← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one,
      hu, one_apply_eq]
  rw [trace_mul_herm hA, traceNorm_eq_sum_abs hA]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨e1, p1⟩ := diag_bounds hW i
  obtain ⟨e2, p2⟩ := diag_bounds hW' i
  have hs := hsum i
  rw [e1, e2] at hs
  have hs' : ((star U * Q * U) i i).re + ((star U * (1 - Q) * U) i i).re = 1 := by
    have := congrArg Complex.re hs; simpa using this
  rw [e1, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have : |((star U * Q * U) i i).re| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  calc _ ≤ 1 * |hA.eigenvalues i| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = _ := one_mul _

/-- The positive spectral projector of a Hermitian matrix. -/
noncomputable def posProj {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) *
    diagonal (fun i => if 0 ≤ hA.eigenvalues i then (1 : ℂ) else 0) *
    star (hA.eigenvectorUnitary : Matrix n n ℂ)

lemma conj_isProjector (U D : Matrix n n ℂ) (hu : star U * U = 1) (hD : star D = D)
    (hDD : D * D = D) : IsProjector (U * D * star U) := by
  refine ⟨?_, ?_⟩
  · rw [← star_eq_conjTranspose]; simp only [star_mul, star_star, hD, Matrix.mul_assoc]
  · rw [show ∀ (P Q R S T : Matrix n n ℂ), P * Q * R * (S * T * R) = P * (Q * (R * S) * T) * R by
      intro P Q R S T; simp only [Matrix.mul_assoc]]
    rw [hu, Matrix.mul_one, hDD]

lemma posProj_isProjector {A : Matrix n n ℂ} (hA : A.IsHermitian) : IsProjector (posProj hA) := by
  apply conj_isProjector _ _ (Unitary.coe_star_mul_self _)
  · rw [star_eq_conjTranspose, diagonal_conjTranspose]; congr 1; funext i
    split_ifs with h <;> simp [h]
  · rw [diagonal_mul_diagonal]; congr 1; funext i; split_ifs with h <;> simp

lemma helstrom_posProj {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (trace (posProj hA * A) - trace ((1 - posProj hA) * A)).re = traceNorm A := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  have hu : star U * U = 1 := Unitary.coe_star_mul_self _
  set D : Matrix n n ℂ := diagonal (fun i => if 0 ≤ hA.eigenvalues i then (1 : ℂ) else 0)
  have h1 : star U * posProj hA * U = D := by
    simp only [posProj]
    rw [show ∀ (P Q R S : Matrix n n ℂ), P * (Q * R * S) * Q = (P * Q) * R * (S * Q) by
      intro P Q R S; simp only [Matrix.mul_assoc]]
    rw [hu, Matrix.one_mul, Matrix.mul_one]
  have h2 : star U * (1 - posProj hA) * U = 1 - D := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu, h1]
  rw [trace_mul_herm hA, trace_mul_herm hA, h1, h2, ← Finset.sum_sub_distrib, Complex.re_sum,
    traceNorm_eq_sum_abs hA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.sub_apply, one_apply_eq, show D i i = if 0 ≤ hA.eigenvalues i then 1 else 0 from
    diagonal_apply_eq _ _]
  split_ifs with h
  · rw [abs_of_nonneg h]; simp
  · rw [abs_of_neg (lt_of_not_ge h)]; simp

/-- **Helstrom / variational formula**: for Hermitian `A`,
`‖A‖₁ = max_{P projector} Re[tr(P A) - tr((1-P) A)]`. -/
theorem traceNorm_isGreatest {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    IsGreatest {r : ℝ | ∃ P : Matrix n n ℂ, IsProjector P ∧
      r = (trace (P * A) - trace ((1 - P) * A)).re} (traceNorm A) := by
  refine ⟨⟨posProj hA, posProj_isProjector hA, (helstrom_posProj hA).symm⟩, ?_⟩
  rintro r ⟨P, hP, rfl⟩
  exact helstrom_le hA hP.posSemidef hP.one_sub.posSemidef

/-- Triangle inequality on Hermitian matrices. -/
theorem traceNorm_add_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  have hAB : (A + B).IsHermitian := hA.add hB
  rw [← helstrom_posProj hAB]
  set P := posProj hAB
  have hP := posProj_isProjector hAB
  have e : (trace (P * (A + B)) - trace ((1 - P) * (A + B))).re =
      (trace (P * A) - trace ((1 - P) * A)).re + (trace (P * B) - trace ((1 - P) * B)).re := by
    simp only [Matrix.mul_add, trace_add, ← Complex.add_re]; ring_nf
  rw [e]
  exact add_le_add (helstrom_le hA hP.posSemidef hP.one_sub.posSemidef)
    (helstrom_le hB hP.posSemidef hP.one_sub.posSemidef)

theorem traceNorm_sub_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (A - B) ≤ traceNorm A + traceNorm B := by
  rw [sub_eq_add_neg, ← traceNorm_neg B]; exact traceNorm_add_le hA hB.neg

theorem traceNorm_sum_le {ι : Type*} (s : Finset ι) (A : ι → Matrix n n ℂ)
    (hA : ∀ i ∈ s, (A i).IsHermitian) :
    traceNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, traceNorm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [(traceNorm_eq_zero_iff (0 : Matrix n n ℂ)).2 rfl]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : (∑ i ∈ s, A i).IsHermitian := by
      have : ∀ t : Finset ι, (∀ i ∈ t, (A i).IsHermitian) → (∑ i ∈ t, A i).IsHermitian := by
        intro t ht
        induction t using Finset.induction_on with
        | empty => simp
        | insert b t hb iht =>
          rw [Finset.sum_insert hb]
          exact (ht b (Finset.mem_insert_self _ _)).add
            (iht fun i hi => ht i (Finset.mem_insert_of_mem hi))
      exact this s fun i hi => hA i (Finset.mem_insert_of_mem hi)
    exact (traceNorm_add_le (hA a (Finset.mem_insert_self _ _)) hs).trans
      (add_le_add le_rfl (ih fun i hi => hA i (Finset.mem_insert_of_mem hi)))

/-! ### Pure states -/

/-- `|ψ⟩⟨ψ|`. -/
def ketbra (ψ : n → ℂ) : Matrix n n ℂ := vecMulVec ψ (star ψ)

lemma ketbra_posSemidef (ψ : n → ℂ) : (ketbra ψ).PosSemidef := posSemidef_vecMulVec_self_star ψ

lemma trace_ketbra (ψ : n → ℂ) : trace (ketbra ψ) = star ψ ⬝ᵥ ψ := by
  simp [ketbra, dotProduct_comm]

lemma ketbra_mul_ketbra (ψ φ : n → ℂ) :
    ketbra ψ * ketbra φ = (star ψ ⬝ᵥ φ) • vecMulVec ψ (star φ) := by
  rw [ketbra, ketbra, vecMulVec_mul_vecMulVec]
  ext i j; simp [vecMulVec_apply, mul_left_comm]

theorem traceNorm_ketbra (ψ : n → ℂ) : traceNorm (ketbra ψ) = (star ψ ⬝ᵥ ψ).re := by
  rw [traceNorm_of_posSemidef (ketbra_posSemidef ψ), trace_ketbra]

lemma ketbra_isProjector {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : IsProjector (ketbra ψ) :=
  ⟨(ketbra_posSemidef ψ).1, by rw [ketbra_mul_ketbra, hψ, one_smul, ketbra]⟩

/-- Orthogonal pure states are perfectly distinguishable: `‖ψψ* - φφ*‖₁ = 2`. -/
theorem traceNorm_ketbra_sub_orthogonal {ψ φ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hφ : star φ ⬝ᵥ φ = 1) (hψφ : star ψ ⬝ᵥ φ = 0) :
    traceNorm (ketbra ψ - ketbra φ) = 2 := by
  have hX : (ketbra ψ - ketbra φ).IsHermitian :=
    (ketbra_posSemidef ψ).1.sub (ketbra_posSemidef φ).1
  apply le_antisymm
  · calc _ ≤ traceNorm (ketbra ψ) + traceNorm (ketbra φ) :=
          traceNorm_sub_le (ketbra_posSemidef ψ).1 (ketbra_posSemidef φ).1
      _ = 2 := by rw [traceNorm_ketbra, traceNorm_ketbra, hψ, hφ]; norm_num
  · have hP := ketbra_isProjector hψ
    have h := (traceNorm_isGreatest hX).2 ⟨ketbra ψ, hP, rfl⟩
    refine le_trans (le_of_eq ?_) h
    have e1 : ketbra ψ * ketbra ψ = ketbra ψ := hP.2
    have e2 : ketbra ψ * ketbra φ = 0 := by rw [ketbra_mul_ketbra, hψφ, zero_smul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, e1, e2, trace_sub, trace_zero,
      trace_ketbra, hψ, hφ]
    norm_num
