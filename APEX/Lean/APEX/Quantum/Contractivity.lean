import APEX.Quantum.OrthogonalNoise

open Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Trace-norm contractivity of Kraus channels and the exact orthogonal-noise diamond value

* `krausDual K Q = Σ_i K_iᴴ Q K_i` (Heisenberg-picture adjoint); `trace_mul_krausMap`:
  `tr(Q · Φ(A)) = tr(Φ*(Q) · A)`; `krausDual_posSemidef`, `one_sub_krausDual`
  (`1 − Φ*(Q) = Φ*(1 − Q)` when `Σ K_iᴴ K_i = 1`), so `Φ*` maps effects to effects.
* `krausMap_isHermitian`, `IsKrausChannel.isHermitian_apply`: channels preserve Hermiticity.
* **`traceNorm_krausMap_le`, `IsKrausChannel.traceNorm_le`** (trace-norm contractivity):
  for a Kraus channel `Φ` and Hermitian `A`, `‖Φ(A)‖₁ ≤ ‖A‖₁` (Helstrom form + duality).
* **`IsKrausChannel.traceNorm_sub_le`** (data processing): `‖Φ A − Φ B‖₁ ≤ ‖A − B‖₁` for
  Hermitian `A, B`.
* `ampliate_comp`: `(Θ ∘ Φ) ⊗ id = (Θ ⊗ id) ∘ (Φ ⊗ id)`;
  **`diamondDist_comp_le`**: `diamondDist (Θ ∘ Φ) (Θ ∘ Ψ) ≤ diamondDist Φ Ψ` for channels
  (post-processing cannot increase the state-input diamond distance), and
  `diamondDist_comp_le_two`.
* **`traceNorm_noisy_sub_ideal_le`**: for every density matrix `ρ` on `n × n`,
  `‖(E ⊗ id)ρ − (V₀ ⊗ id)ρ‖₁ ≤ 2 (1 − (1 − ℓ) p_{i₀})` (no orthogonality needed). Proof:
  with `a = (1 − ℓ) p_{i₀}`, `A − a B` is PSD (it is the Kraus sum without the `i₀` term), and
  `A − B = (A − aB) − (1 − a) B`, so the triangle inequality gives `(1 − a) + (1 − a)`.
* **`diamondDist_noisy_ideal_le`** and **`diamondDist_noisy_ideal_eq`**:
  `diamondDist E V₀ = 2 (1 − (1 − ℓ) p_{i₀})` for Hilbert–Schmidt-orthogonal unitaries.

As in `OrthogonalNoise`, `diamondDist` is the state-input version with ancilla dimension equal
to the input dimension; its identification with the usual diamond norm is not formalised.
-/

namespace APEX.Quantum

section General

variable {n m p : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype p] [DecidableEq p]

/-- The Heisenberg-picture adjoint `Q ↦ Σ_i K_iᴴ Q K_i` of a Kraus map. -/
def krausDual {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ) (Q : Matrix m m ℂ) :
    Matrix n n ℂ :=
  ∑ i, (K i)ᴴ * Q * K i

/-- Duality `tr(Q Φ(A)) = tr(Φ*(Q) A)`. -/
theorem trace_mul_krausMap {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ) (Q : Matrix m m ℂ)
    (A : Matrix n n ℂ) : trace (Q * krausMap K A) = trace (krausDual K Q * A) := by
  simp only [krausMap, krausDual, Matrix.mul_sum, Matrix.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Q * (K i * A * (K i)ᴴ) = (Q * K i * A) * (K i)ᴴ by simp only [Matrix.mul_assoc],
    trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma krausDual_posSemidef {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ) {Q : Matrix m m ℂ}
    (hQ : Q.PosSemidef) : (krausDual K Q).PosSemidef :=
  posSemidef_sum _ fun i _ => hQ.conjTranspose_mul_mul_same (K i)

lemma one_sub_krausDual {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (Q : Matrix m m ℂ) :
    1 - krausDual K Q = krausDual K (1 - Q) := by
  simp only [krausDual, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Finset.sum_sub_distrib,
    hK]

lemma krausMap_isHermitian {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (krausMap K A).IsHermitian :=
  isSelfAdjoint_sum _ fun i _ => isHermitian_mul_mul_conjTranspose (K i) hA

theorem IsKrausChannel.isHermitian_apply {Φ : Matrix n n ℂ → Matrix m m ℂ}
    (hΦ : IsKrausChannel Φ) {A : Matrix n n ℂ} (hA : A.IsHermitian) : (Φ A).IsHermitian := by
  obtain ⟨ι, _, K, hK, rfl⟩ := hΦ; exact krausMap_isHermitian K hA

/-- **Trace-norm contractivity** of a normalised Kraus map on Hermitian inputs. -/
theorem traceNorm_krausMap_le {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (krausMap K A) ≤ traceNorm A := by
  have hB := krausMap_isHermitian K hA
  rw [← helstrom_posProj hB]
  have hP := posProj_isProjector hB
  rw [trace_mul_krausMap, trace_mul_krausMap, ← one_sub_krausDual K hK]
  refine helstrom_le hA (krausDual_posSemidef K hP.posSemidef) ?_
  rw [one_sub_krausDual K hK]
  exact krausDual_posSemidef K hP.one_sub.posSemidef

/-- **Trace-norm contractivity of channels**: `‖Φ(A)‖₁ ≤ ‖A‖₁` for Hermitian `A`. -/
theorem IsKrausChannel.traceNorm_le {Φ : Matrix n n ℂ → Matrix m m ℂ} (hΦ : IsKrausChannel Φ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : traceNorm (Φ A) ≤ traceNorm A := by
  obtain ⟨ι, _, K, hK, rfl⟩ := hΦ; exact traceNorm_krausMap_le K hK hA

lemma IsKrausChannel.map_sub {Φ : Matrix n n ℂ → Matrix m m ℂ} (hΦ : IsKrausChannel Φ)
    (A B : Matrix n n ℂ) : Φ A - Φ B = Φ (A - B) := by
  obtain ⟨ι, _, K, hK, rfl⟩ := hΦ
  simp only [krausMap, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

/-- **Data processing** for the trace distance (Hermitian inputs). -/
theorem IsKrausChannel.traceNorm_sub_le {Φ : Matrix n n ℂ → Matrix m m ℂ}
    (hΦ : IsKrausChannel Φ) {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (Φ A - Φ B) ≤ traceNorm (A - B) := by
  rw [hΦ.map_sub]; exact hΦ.traceNorm_le (hA.sub hB)

lemma ampliate_comp (Φ : Matrix n n ℂ → Matrix m m ℂ) (Θ : Matrix m m ℂ → Matrix p p ℂ)
    (k : Type*) (X : Matrix (n × k) (n × k) ℂ) :
    ampliate (Θ ∘ Φ) k X = ampliate Θ k (ampliate Φ k X) := rfl

end General

section Diamond

variable {n m p : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype p] [DecidableEq p]

/-- Post-processing by a channel cannot increase the (state-input) diamond distance. -/
theorem diamondDist_comp_le [Nonempty n] {Φ Ψ : Matrix n n ℂ → Matrix m m ℂ}
    {Θ : Matrix m m ℂ → Matrix p p ℂ} (hΦ : IsKrausChannel Φ) (hΨ : IsKrausChannel Ψ)
    (hΘ : IsKrausChannel Θ) : diamondDist (Θ ∘ Φ) (Θ ∘ Ψ) ≤ diamondDist Φ Ψ := by
  refine csSup_le ⟨_, ketbra (omega n), ketbra_posSemidef _, by rw [trace_ketbra, omega_norm],
    rfl⟩ ?_
  rintro r ⟨σ, hσ, hσt, rfl⟩
  rw [ampliate_comp, ampliate_comp]
  have h1 := (hΦ.tensorId (k := n)).posSemidef_apply hσ
  have h2 := (hΨ.tensorId (k := n)).posSemidef_apply hσ
  exact ((hΘ.tensorId (k := n)).traceNorm_sub_le h1.1 h2.1).trans (le_diamondDist hΦ hΨ hσ hσt)

theorem diamondDist_comp_le_two [Nonempty n] {Φ Ψ : Matrix n n ℂ → Matrix m m ℂ}
    {Θ : Matrix m m ℂ → Matrix p p ℂ} (hΦ : IsKrausChannel Φ) (hΨ : IsKrausChannel Ψ)
    (hΘ : IsKrausChannel Θ) : diamondDist (Θ ∘ Φ) (Θ ∘ Ψ) ≤ 2 :=
  (diamondDist_comp_le hΦ hΨ hΘ).trans (diamondDist_le_two hΦ hΨ)

end Diamond

section Noisy

variable {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Upper bound on every density input:
`‖(E ⊗ id)ρ − (V₀ ⊗ id)ρ‖₁ ≤ 2 (1 − (1 − ℓ) p_{i₀})`. -/
theorem traceNorm_noisy_sub_ideal_le {U : ι → Matrix n n ℂ} (hU : ∀ i, U i ∈ unitaryGroup n ℂ)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1)
    (i₀ : ι) {ρ : Matrix (n × n) (n × n) ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    traceNorm (ampliate (noisyChannel U p ℓ) n ρ - ampliate (idealChannel (U i₀)) n ρ) ≤
      2 * (1 - (1 - ℓ) * p i₀) := by
  have hp1 : p i₀ ≤ 1 := by
    rw [← hsum]; exact Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ _)
  have ha0 : 0 ≤ (1 - ℓ) * p i₀ := mul_nonneg (by linarith) (hp i₀)
  have ha1 : (1 - ℓ) * p i₀ ≤ 1 := by nlinarith
  obtain ⟨hA, tA⟩ := ((noisyChannel_isKraus hU hp hsum hℓ0 hℓ1).tensorId (k := n)).density hρ htr
  obtain ⟨hB, tB⟩ := ((idealChannel_isKraus (hU i₀)).tensorId (k := n)).density hρ htr
  set A := ampliate (noisyChannel U p ℓ) n ρ with hAdef
  set B := ampliate (idealChannel (U i₀)) n ρ with hBdef
  set a : ℝ := (1 - ℓ) * p i₀ with ha
  set T : ι ⊕ n → Matrix ((n ⊕ Unit) × n) ((n ⊕ Unit) × n) ℂ := fun x =>
    (noiseKraus U p ℓ x ⊗ₖ (1 : Matrix n n ℂ)) * ρ *
      (noiseKraus U p ℓ x ⊗ₖ (1 : Matrix n n ℂ))ᴴ with hT
  have hAT : A = ∑ x, T x := by
    rw [hAdef, noisyChannel, ampliate_krausMap]; rfl
  have hTB : T (Sum.inl i₀) = (a : ℂ) • B := by
    rw [hBdef, idealChannel, ampliate_krausMap, krausMap, Fintype.sum_unique]
    simp only [hT, noiseKraus, Sum.elim_inl, smul_kronecker, conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha0]
  have hD : (A - (a : ℂ) • B).PosSemidef := by
    rw [hAT, ← Finset.add_sum_erase _ _ (Finset.mem_univ (Sum.inl i₀)), hTB, add_sub_cancel_left]
    exact posSemidef_sum _ fun x _ => hρ.mul_mul_conjTranspose_same _
  have hE : (((1 - a : ℝ) : ℂ) • B).PosSemidef := hB.smul (by exact_mod_cast sub_nonneg.2 ha1)
  have hsplit : A - B = (A - (a : ℂ) • B) - ((1 - a : ℝ) : ℂ) • B := by
    push_cast; rw [sub_smul, one_smul]; abel
  rw [hsplit]
  refine (traceNorm_sub_le hD.1 hE.1).trans (le_of_eq ?_)
  rw [traceNorm_of_posSemidef hD, traceNorm_of_posSemidef hE, trace_sub, trace_smul, trace_smul,
    tA, tB]
  simp only [smul_eq_mul, mul_one, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  ring

/-- **Upper bound in the orthogonal-noise diamond formula** (no orthogonality needed). -/
theorem diamondDist_noisy_ideal_le [Nonempty n] {U : ι → Matrix n n ℂ}
    (hU : ∀ i, U i ∈ unitaryGroup n ℂ) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (i₀ : ι) :
    diamondDist (noisyChannel U p ℓ) (idealChannel (U i₀)) ≤ 2 * (1 - (1 - ℓ) * p i₀) := by
  refine csSup_le ⟨_, ketbra (omega n), ketbra_posSemidef _, by rw [trace_ketbra, omega_norm],
    rfl⟩ ?_
  rintro r ⟨σ, hσ, hσt, rfl⟩
  exact traceNorm_noisy_sub_ideal_le hU hp hsum hℓ0 hℓ1 i₀ hσ hσt

/-- **Exact orthogonal-noise diamond value**: for Hilbert–Schmidt-orthogonal unitaries,
`diamondDist E V₀ = 2 (1 − (1 − ℓ) p_{i₀})`. -/
theorem diamondDist_noisy_ideal_eq [Nonempty n] {U : ι → Matrix n n ℂ}
    (hU : ∀ i, U i ∈ unitaryGroup n ℂ) (hHS : ∀ i j, i ≠ j → trace ((U i)ᴴ * U j) = 0)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1)
    (i₀ : ι) :
    diamondDist (noisyChannel U p ℓ) (idealChannel (U i₀)) = 2 * (1 - (1 - ℓ) * p i₀) :=
  le_antisymm (diamondDist_noisy_ideal_le hU hp hsum hℓ0 hℓ1 i₀)
    (diamondDist_noisy_ideal_ge hU hHS hp hsum hℓ0 hℓ1 i₀)

end Noisy

end APEX.Quantum

