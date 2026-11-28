import APEX.Quantum.TraceNorm
import Mathlib.LinearAlgebra.Matrix.Kronecker

open Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

/-!
# Kraus channels (CPTP maps) on matrix algebras

Mathlib has no quantum channels. For `K : ι → Matrix m n ℂ` (`ι` finite) we set
`krausMap K ρ = Σ_i K_i ρ K_iᴴ` and `IsKrausChannel Φ :↔ ∃ ι K, Σ K_iᴴ K_i = 1 ∧ Φ = krausMap K`.

* `trace_krausMap` / `IsKrausChannel.trace_apply`: trace preservation.
* `posSemidef_krausMap` / `IsKrausChannel.posSemidef_apply`: positivity; `IsKrausChannel.density`.
* `ampliate Φ k`: `Φ ⊗ id_k` defined blockwise from `Φ` alone,
  `(Φ⊗id)(X)_{(y,a),(y',b)} = Φ(X_{(·,a),(·,b)})_{y y'}`;
  `ampliate_krausMap`: for Kraus maps it is the Kraus map with operators `K_i ⊗ₖ 1`;
  `ampliate_krausMap_kronecker`: `(Φ⊗id)(A ⊗ B) = Φ(A) ⊗ B`.
* `IsKrausChannel.tensorId`: `Φ ⊗ id_k` is a channel; **`IsKrausChannel.completelyPositive`**:
  `Φ ⊗ id_k` maps every PSD matrix on `n × k` (not only product ones) to a PSD matrix.
* `isKrausChannel_isometry`, `isKrausChannel_unitary`, `isKrausChannel_id`,
  `IsKrausChannel.comp` (composition), `IsKrausChannel.convex` (convex mixtures).

Not done: Choi–Kraus equivalence (CP ⇒ Kraus form), Stinespring. (Trace-norm contractivity on Hermitian
inputs: `APEX/Quantum/Contractivity.lean`.)
-/

namespace APEX.Quantum

variable {n m p k : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype p] [DecidableEq p] [Fintype k] [DecidableEq k]

/-- The Kraus map `ρ ↦ Σ_i K_i ρ K_iᴴ` (from `n`-level to `m`-level matrices). -/
def krausMap {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ) (ρ : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ i, K i * ρ * (K i)ᴴ

/-- `Φ` is a quantum channel given by a finite Kraus family with `Σ K_iᴴ K_i = 1`. -/
def IsKrausChannel (Φ : Matrix n n ℂ → Matrix m m ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (K : ι → Matrix m n ℂ), ∑ i, (K i)ᴴ * K i = 1 ∧ Φ = krausMap K

lemma krausMap_add {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ) (A B : Matrix n n ℂ) :
    krausMap K (A + B) = krausMap K A + krausMap K B := by
  simp [krausMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma krausMap_smul {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ) (c : ℂ) (A : Matrix n n ℂ) :
    krausMap K (c • A) = c • krausMap K A := by
  simp [krausMap, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

/-- Trace preservation. -/
theorem trace_krausMap {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (ρ : Matrix n n ℂ) : trace (krausMap K ρ) = trace ρ := by
  unfold krausMap
  rw [trace_sum]
  have : ∀ i, trace (K i * ρ * (K i)ᴴ) = trace ((K i)ᴴ * K i * ρ) := by
    intro i; rw [trace_mul_comm, Matrix.mul_assoc]
  simp_rw [this, ← trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

/-- Positivity preservation. -/
theorem posSemidef_krausMap {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) : (krausMap K ρ).PosSemidef :=
  posSemidef_sum _ fun i _ => hρ.mul_mul_conjTranspose_same (K i)

theorem IsKrausChannel.trace_apply {Φ : Matrix n n ℂ → Matrix m m ℂ} (hΦ : IsKrausChannel Φ)
    (ρ : Matrix n n ℂ) : trace (Φ ρ) = trace ρ := by
  obtain ⟨ι, _, K, hK, rfl⟩ := hΦ; exact trace_krausMap K hK ρ

theorem IsKrausChannel.posSemidef_apply {Φ : Matrix n n ℂ → Matrix m m ℂ}
    (hΦ : IsKrausChannel Φ) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) : (Φ ρ).PosSemidef := by
  obtain ⟨ι, _, K, hK, rfl⟩ := hΦ; exact posSemidef_krausMap K hρ

/-- Channels map density matrices to density matrices. -/
theorem IsKrausChannel.density {Φ : Matrix n n ℂ → Matrix m m ℂ} (hΦ : IsKrausChannel Φ)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    (Φ ρ).PosSemidef ∧ trace (Φ ρ) = 1 :=
  ⟨hΦ.posSemidef_apply hρ, by rw [hΦ.trace_apply, htr]⟩

/-! ### Ampliation `Φ ⊗ id_k` and complete positivity -/

/-- `(Φ ⊗ id_k)(X)`, defined blockwise from `Φ` alone:
`(Φ ⊗ id)(X)_{(y,a),(y',b)} = Φ(X_{(·,a),(·,b)})_{y,y'}`. -/
def ampliate (Φ : Matrix n n ℂ → Matrix m m ℂ) (k : Type*) (X : Matrix (n × k) (n × k) ℂ) :
    Matrix (m × k) (m × k) ℂ :=
  Matrix.of fun P Q => Φ (Matrix.of fun x x' => X (x, P.2) (x', Q.2)) P.1 Q.1

/-- For a Kraus map, the ampliation is the Kraus map with Kraus operators `K_i ⊗ 1`. -/
theorem ampliate_krausMap {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ)
    (X : Matrix (n × k) (n × k) ℂ) :
    ampliate (krausMap K) k X = krausMap (fun i => K i ⊗ₖ (1 : Matrix k k ℂ)) X := by
  ext P Q
  obtain ⟨y, a⟩ := P
  obtain ⟨y', b⟩ := Q
  unfold ampliate krausMap
  rw [of_apply, Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Matrix.of_apply, Finset.sum_mul]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero, apply_ite star, star_zero]

theorem sum_kronecker_one {ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ) :
    (∑ i ∈ s, A i) ⊗ₖ (1 : Matrix k k ℂ) = ∑ i ∈ s, A i ⊗ₖ (1 : Matrix k k ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_kronecker, ih]

/-- The Kraus family `K_i ⊗ 1` of `Φ ⊗ id` is again normalised. -/
theorem kraus_kronecker_one_sum {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    ∑ i, (K i ⊗ₖ (1 : Matrix k k ℂ))ᴴ * (K i ⊗ₖ (1 : Matrix k k ℂ)) = 1 := by
  simp_rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [← sum_kronecker_one, hK, one_kronecker_one]

/-- `Φ ⊗ id_k` is again a Kraus channel. -/
theorem IsKrausChannel.tensorId {Φ : Matrix n n ℂ → Matrix m m ℂ} (hΦ : IsKrausChannel Φ) :
    IsKrausChannel (ampliate Φ k) := by
  obtain ⟨ι, _, K, hK, rfl⟩ := hΦ
  exact ⟨ι, inferInstance, fun i => K i ⊗ₖ (1 : Matrix k k ℂ), kraus_kronecker_one_sum K hK,
    funext fun X => ampliate_krausMap K X⟩

/-- **Complete positivity**: for every finite ancilla `k`, `Φ ⊗ id_k` maps positive semidefinite
matrices on `n × k` to positive semidefinite matrices on `m × k`. -/
theorem IsKrausChannel.completelyPositive {Φ : Matrix n n ℂ → Matrix m m ℂ}
    (hΦ : IsKrausChannel Φ) {X : Matrix (n × k) (n × k) ℂ} (hX : X.PosSemidef) :
    (ampliate Φ k X).PosSemidef :=
  hΦ.tensorId.posSemidef_apply hX

theorem sum_kronecker' {ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ) (B : Matrix k k ℂ) :
    (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, A i ⊗ₖ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_kronecker, ih]

/-- `(Φ ⊗ id)(A ⊗ B) = Φ(A) ⊗ B` for a Kraus map. -/
theorem ampliate_krausMap_kronecker {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ)
    (A : Matrix n n ℂ) (B : Matrix k k ℂ) :
    ampliate (krausMap K) k (A ⊗ₖ B) = krausMap K A ⊗ₖ B := by
  rw [ampliate_krausMap, krausMap, krausMap, sum_kronecker']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

/-! ### Closure properties -/

/-- Isometric channels `ρ ↦ V ρ Vᴴ` with `Vᴴ V = 1`. -/
theorem isKrausChannel_isometry (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) :
    IsKrausChannel (fun ρ : Matrix n n ℂ => V * ρ * Vᴴ) :=
  ⟨Unit, inferInstance, fun _ => V, by simpa using hV, by funext ρ; simp [krausMap]⟩

/-- Unitary channels `ρ ↦ U ρ U*`. -/
theorem isKrausChannel_unitary (U : unitaryGroup n ℂ) :
    IsKrausChannel (fun ρ : Matrix n n ℂ => (U : Matrix n n ℂ) * ρ * star (U : Matrix n n ℂ)) := by
  have := isKrausChannel_isometry (U : Matrix n n ℂ)
    (by rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self U)
  simpa [star_eq_conjTranspose] using this

/-- The identity channel. -/
theorem isKrausChannel_id : IsKrausChannel (fun ρ : Matrix n n ℂ => ρ) := by
  simpa using isKrausChannel_isometry (1 : Matrix n n ℂ) (by simp)

/-- Composition of channels is a channel. -/
theorem IsKrausChannel.comp {Φ : Matrix n n ℂ → Matrix m m ℂ} {Ψ : Matrix m m ℂ → Matrix p p ℂ}
    (hΦ : IsKrausChannel Φ) (hΨ : IsKrausChannel Ψ) : IsKrausChannel (Ψ ∘ Φ) := by
  obtain ⟨ι, _, K, hK, rfl⟩ := hΦ
  obtain ⟨κ, _, F, hF, rfl⟩ := hΨ
  refine ⟨ι × κ, inferInstance, fun q => F q.2 * K q.1, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    have : ∀ i, ∑ j, (F j * K i)ᴴ * (F j * K i) = (K i)ᴴ * (∑ j, (F j)ᴴ * F j) * K i := by
      intro i
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    simp_rw [this, hF, Matrix.mul_one, hK]
  · funext ρ
    simp only [Function.comp_apply, krausMap, Fintype.sum_prod_type, Matrix.mul_sum,
      Matrix.sum_mul, conjTranspose_mul, Matrix.mul_assoc]
    exact Finset.sum_comm

/-- Convex mixtures of channels are channels. -/
theorem IsKrausChannel.convex {Φ Ψ : Matrix n n ℂ → Matrix m m ℂ}
    (hΦ : IsKrausChannel Φ) (hΨ : IsKrausChannel Ψ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsKrausChannel (fun ρ => (t : ℂ) • Φ ρ + ((1 - t : ℝ) : ℂ) • Ψ ρ) := by
  obtain ⟨ι, _, K, hK, rfl⟩ := hΦ
  obtain ⟨κ, _, F, hF, rfl⟩ := hΨ
  have hs : ∀ s : ℝ, 0 ≤ s → ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) = (s : ℂ) := by
    intro s hs
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs]
  have hstar : ∀ s : ℝ, star (s : ℂ) = (s : ℂ) := fun s => Complex.conj_ofReal s
  refine ⟨ι ⊕ κ, inferInstance,
    Sum.elim (fun i => ((Real.sqrt t : ℝ) : ℂ) • K i) (fun j => ((Real.sqrt (1 - t) : ℝ) : ℂ) • F j),
    ?_, ?_⟩
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, ← Finset.smul_sum, hK, hF, hstar, hs t ht0, hs (1 - t) (by linarith)]
    rw [← add_smul]; simp
  · funext ρ
    simp only [krausMap, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.smul_sum, hstar, hs t ht0,
      hs (1 - t) (by linarith)]
