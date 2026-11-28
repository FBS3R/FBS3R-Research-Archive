import APEX.Quantum.CPTP
import Mathlib.Tactic.LinearCombination

open Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
# Orthogonal-noise channel vs. ideal unitary: the maximally-entangled-input value

Setting (`n : Type`, `d = card n ≥ 1`): unitaries `U : ι → M_d` with Hilbert–Schmidt orthogonality
`tr(U_iᴴ U_j) = 0` for `i ≠ j` (the diagonal `tr(U_iᴴU_i) = d` follows from unitarity), a
probability vector `p`, an erasure probability `ℓ ∈ [0,1]`.

* Output space `n ⊕ Unit` (`d + 1` levels; `Sum.inr ()` is the erasure flag).
* `noisyChannel U p ℓ` : Kraus channel with operators `√((1-ℓ)p_i)·(U_i ⊕ 0)` and
  `√ℓ·|flag⟩⟨j|`; `noisyChannel_apply`: block form
  `E(ρ) = [[(1-ℓ) Σ_i p_i U_i ρ U_iᴴ, 0], [0, ℓ tr ρ]]`; `noisyChannel_isKraus`: it is a channel.
* `idealChannel U₀` : `ρ ↦ (U₀ ⊕ 0) ρ (U₀ ⊕ 0)ᴴ` (`idealChannel_apply`, `idealChannel_isKraus`).
* `omega n` : the maximally entangled vector `d^{-1/2} Σ_i |i i⟩`, `Φ⁺ = ketbra (omega n)`.
* **`traceNorm_noisy_sub_ideal_maxEnt`**:
  `‖(E ⊗ id_n)(Φ⁺) − (V₀ ⊗ id_n)(Φ⁺)‖₁ = 2 (1 − (1 − ℓ) p_{i₀})` (exact equality:
  `≤` by the triangle inequality on an explicit decomposition into rank-one terms built from the
  orthonormal family `(U_i ⊗ 1)|Φ⁺⟩` and the flag vectors; `≥` by the Helstrom test with the
  projector `1 − |ψ₀⟩⟨ψ₀|`, `ψ₀ = (U_{i₀} ⊗ 1)|Φ⁺⟩`).
* `diamondDist Φ Ψ` := `sup_ρ ‖(Φ⊗id_n)(ρ) − (Ψ⊗id_n)(ρ)‖₁` over density matrices `ρ` on `n × n`
  (ancilla dimension = input dimension). `le_diamondDist`, `diamondDist_le_two`, and
  **`diamondDist_noisy_ideal_ge`**: `2 (1 − (1 − ℓ) p_{i₀}) ≤ diamondDist E V₀`.

## Not proved here
* The matching **upper bound** `diamondDist E V₀ ≤ 2 (1 − (1 − ℓ) p_{i₀})` (needs, e.g.,
  a bound valid for every input state, via trace-norm contractivity of CPTP maps / a
  Holevo–Helstrom argument for arbitrary inputs; trace-norm contractivity is not formalised).
* The identification of `diamondDist` with the usual diamond norm `‖E − V₀‖◇` (sup over all
  trace-norm-≤1 operators with arbitrary ancilla). That ancilla dimension `d` suffices and that
  density-matrix inputs suffice for Hermiticity-preserving maps are standard theorems
  (e.g. Watrous, TQI Thm 3.46/3.51) that are not formalised here.
-/

namespace APEX.Quantum

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Embed an `n × n` matrix as the top rows of an `(n ⊕ Unit) × n` matrix. -/
def embed (M : Matrix n n ℂ) : Matrix (n ⊕ Unit) n ℂ :=
  Matrix.of fun x t => Sum.elim (fun s => M s t) (fun _ => 0) x

/-- `|flag⟩⟨j|`. -/
def flagOp (j : n) : Matrix (n ⊕ Unit) n ℂ :=
  Matrix.of fun x t => Sum.elim (fun _ => 0) (fun _ => if t = j then 1 else 0) x

lemma embed_ct_mul_embed (A B : Matrix n n ℂ) : (embed A)ᴴ * embed B = Aᴴ * B := by
  ext t t'; simp [Matrix.mul_apply, embed, Fintype.sum_sum_type]

lemma embed_ct_mul_flag (A : Matrix n n ℂ) (j : n) : (embed A)ᴴ * flagOp j = 0 := by
  ext t t'; simp [Matrix.mul_apply, embed, flagOp, Fintype.sum_sum_type]

lemma flag_ct_mul_embed (A : Matrix n n ℂ) (j : n) : (flagOp j)ᴴ * embed A = 0 := by
  ext t t'; simp [Matrix.mul_apply, embed, flagOp, Fintype.sum_sum_type]

lemma sum_flag_ct_mul_flag : ∑ j : n, (flagOp j)ᴴ * flagOp j = 1 := by
  ext t t'
  simp only [Matrix.sum_apply, Matrix.mul_apply, flagOp, conjTranspose_apply, of_apply,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, star_zero, zero_mul, Finset.sum_const_zero,
    zero_add, Fintype.sum_unique, apply_ite star, star_one, mul_ite, ite_mul, mul_one, one_mul,
    mul_zero, zero_mul]
  by_cases h : t = t'
  · subst h; simp [Matrix.one_apply]
  · rw [Matrix.one_apply_ne h]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h1 : t' = j
    · subst h1; simp [h]
    · simp [h1]

lemma trace_flag_ct_mul_flag (j : n) : trace ((flagOp j)ᴴ * flagOp j) = 1 := by
  simp [trace, Matrix.mul_apply, flagOp, Fintype.sum_sum_type]

/-! ### The maximally entangled state -/

/-- `|Φ⁺⟩ = d^{-1/2} Σ_i |i⟩|i⟩` on `n × n`. -/
noncomputable def omega (n : Type*) [Fintype n] [DecidableEq n] : n × n → ℂ :=
  fun q => if q.1 = q.2 then (((Real.sqrt (Fintype.card n))⁻¹ : ℝ) : ℂ) else 0

/-- `(M ⊗ 1)|Φ⁺⟩` for `M : Matrix (n ⊕ Unit) n ℂ`. -/
noncomputable def vecOf (M : Matrix (n ⊕ Unit) n ℂ) : (n ⊕ Unit) × n → ℂ :=
  (M ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ omega n

lemma vecOf_apply (M : Matrix (n ⊕ Unit) n ℂ) (q : (n ⊕ Unit) × n) :
    vecOf M q = M q.1 q.2 * (((Real.sqrt (Fintype.card n))⁻¹ : ℝ) : ℂ) := by
  obtain ⟨x, a⟩ := q
  simp only [vecOf, mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, one_apply,
    omega, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_eq_single a]
  · simp
  · intro t _ ht; simp [Matrix.one_apply_ne (Ne.symm ht)]
  · simp

lemma vecOf_smul (c : ℂ) (M : Matrix (n ⊕ Unit) n ℂ) : vecOf (c • M) = c • vecOf M := by
  funext q; simp [vecOf_apply, mul_assoc]

lemma inner_vecOf [Nonempty n] (M N : Matrix (n ⊕ Unit) n ℂ) :
    star (vecOf M) ⬝ᵥ vecOf N = trace (Mᴴ * N) / (Fintype.card n : ℂ) := by
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hs : star ((((Real.sqrt (Fintype.card n))⁻¹ : ℝ) : ℂ)) *
      (((Real.sqrt (Fintype.card n))⁻¹ : ℝ) : ℂ) = 1 / (Fintype.card n : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt hd.le]
    simp
  simp only [dotProduct, Pi.star_apply, vecOf_apply, star_mul', trace, diag, Matrix.mul_apply,
    conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm, div_eq_mul_one_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hs]; ring

lemma ketbra_real_smul (r : ℝ) (v : (n ⊕ Unit) × n → ℂ) :
    ketbra ((r : ℂ) • v) = ((r ^ 2 : ℝ) : ℂ) • ketbra v := by
  ext i j
  simp only [ketbra, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul,
    star_mul', Complex.star_def, Complex.conj_ofReal]
  push_cast; ring

lemma krausMap_ketbra {m k : Type*} [Fintype m] [Fintype k] {ι : Type*} [Fintype ι]
    (K : ι → Matrix m k ℂ) (v : k → ℂ) :
    krausMap K (ketbra v) = ∑ i, ketbra (K i *ᵥ v) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ketbra, ketbra, mul_vecMulVec, vecMulVec_mul, star_mulVec]

lemma trace_ketbra_mul_ketbra {m : Type*} [Fintype m] [DecidableEq m] (ψ v : m → ℂ) :
    trace (ketbra ψ * ketbra v) = (star ψ ⬝ᵥ v) * (star v ⬝ᵥ ψ) := by
  rw [ketbra_mul_ketbra, trace_smul, trace_vecMulVec, dotProduct_comm ψ, smul_eq_mul]

lemma traceNorm_smul_ketbra {m : Type*} [Fintype m] [DecidableEq m] {r : ℝ} (hr : 0 ≤ r)
    (v : m → ℂ) : traceNorm ((r : ℂ) • ketbra v) = r * (star v ⬝ᵥ v).re := by
  have hP : ((r : ℂ) • ketbra v).PosSemidef :=
    (ketbra_posSemidef v).smul (by exact_mod_cast hr)
  rw [traceNorm_of_posSemidef hP, trace_smul, trace_ketbra, smul_eq_mul, Complex.re_ofReal_mul]

/-! ### The orthogonal-noise channel with an erasure flag -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Kraus operators of `E(ρ) = (1-ℓ) Σ_i p_i U_i ρ U_iᴴ ⊕ ℓ tr(ρ) |flag⟩⟨flag|`:
`√((1-ℓ)p_i) · (U_i ⊕ 0)` and `√ℓ · |flag⟩⟨j|`. -/
noncomputable def noiseKraus (U : ι → Matrix n n ℂ) (p : ι → ℝ) (ℓ : ℝ) :
    ι ⊕ n → Matrix (n ⊕ Unit) n ℂ :=
  Sum.elim (fun i => ((Real.sqrt ((1 - ℓ) * p i) : ℝ) : ℂ) • embed (U i))
    (fun j => ((Real.sqrt ℓ : ℝ) : ℂ) • flagOp j)

/-- The noisy channel `E : M_d → M_{d+1}`. -/
noncomputable def noisyChannel (U : ι → Matrix n n ℂ) (p : ι → ℝ) (ℓ : ℝ) :
    Matrix n n ℂ → Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ :=
  krausMap (noiseKraus U p ℓ)

/-- The ideal channel `ρ ↦ U₀ ρ U₀ᴴ`, with output embedded in the top block of `M_{d+1}`. -/
noncomputable def idealChannel (U₀ : Matrix n n ℂ) :
    Matrix n n ℂ → Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ :=
  krausMap (fun _ : Unit => embed U₀)

theorem idealChannel_isKraus {U₀ : Matrix n n ℂ} (hU₀ : U₀ ∈ unitaryGroup n ℂ) :
    IsKrausChannel (idealChannel U₀) := by
  refine ⟨Unit, inferInstance, fun _ => embed U₀, ?_, rfl⟩
  rw [Fintype.sum_unique, embed_ct_mul_embed, ← star_eq_conjTranspose]
  exact (mem_unitaryGroup_iff').1 hU₀

theorem noisyChannel_isKraus {U : ι → Matrix n n ℂ} (hU : ∀ i, U i ∈ unitaryGroup n ℂ)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) :
    IsKrausChannel (noisyChannel U p ℓ) := by
  refine ⟨ι ⊕ n, inferInstance, noiseKraus U p ℓ, ?_, rfl⟩
  have hstar : ∀ s : ℝ, star (s : ℂ) = (s : ℂ) := fun s => Complex.conj_ofReal s
  have hsq : ∀ s : ℝ, 0 ≤ s → ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) = (s : ℂ) := by
    intro s hs; rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs]
  rw [Fintype.sum_sum_type]
  simp only [noiseKraus, Sum.elim_inl, Sum.elim_inr, conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hstar, embed_ct_mul_embed]
  have hUU : ∀ i, (U i)ᴴ * U i = 1 := fun i => by
    rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff').1 (hU i)
  have hsq' : ∀ i, ((Real.sqrt ((1 - ℓ) * p i) : ℝ) : ℂ) * ((Real.sqrt ((1 - ℓ) * p i) : ℝ) : ℂ)
      = (((1 - ℓ) * p i : ℝ) : ℂ) := fun i => hsq _ (mul_nonneg (by linarith) (hp i))
  simp only [hUU, ← Finset.smul_sum, sum_flag_ct_mul_flag, hsq', hsq ℓ hℓ0]
  rw [← Finset.sum_smul, ← add_smul]
  have : ∑ i, (((1 - ℓ) * p i : ℝ) : ℂ) + (ℓ : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, ← Finset.mul_sum, hsum]; push_cast; ring
  rw [this, one_smul]

/-- **Orthogonal-noise lower bound on the maximally entangled input.**
For Hilbert–Schmidt-orthogonal unitaries `U_i` (`tr(U_iᴴ U_j) = 0` for `i ≠ j`), a probability
vector `p`, an erasure probability `ℓ ∈ [0,1]`, and the ideal channel `V₀ = U_{i₀} · U_{i₀}ᴴ`:
`‖(E ⊗ id − V₀ ⊗ id)(Φ⁺)‖₁ = 2 (1 − (1 − ℓ) p_{i₀})`. -/
theorem traceNorm_noisy_sub_ideal_maxEnt [Nonempty n] {U : ι → Matrix n n ℂ}
    (hU : ∀ i, U i ∈ unitaryGroup n ℂ) (hHS : ∀ i j, i ≠ j → trace ((U i)ᴴ * U j) = 0)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1)
    (i₀ : ι) :
    traceNorm (ampliate (noisyChannel U p ℓ) n (ketbra (omega n)) -
      ampliate (idealChannel (U i₀)) n (ketbra (omega n))) = 2 * (1 - (1 - ℓ) * p i₀) := by
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hdC : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  -- inner products
  set e : ι → (n ⊕ Unit) × n → ℂ := fun i => vecOf (embed (U i)) with he
  set f : n → (n ⊕ Unit) × n → ℂ := fun j => vecOf (flagOp j) with hf
  have hUU : ∀ i, (U i)ᴴ * U i = 1 := fun i => by
    rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff').1 (hU i)
  have hee : ∀ i j, star (e i) ⬝ᵥ e j = if i = j then 1 else 0 := by
    intro i j
    simp only [he, inner_vecOf, embed_ct_mul_embed]
    split_ifs with h
    · subst h; rw [hUU, trace_one]; exact div_self hdC
    · rw [hHS i j h, zero_div]
  have hff : ∀ j, star (f j) ⬝ᵥ f j = ((1 / (Fintype.card n : ℝ) : ℝ) : ℂ) := by
    intro j; simp only [hf, inner_vecOf, trace_flag_ct_mul_flag]; push_cast; ring
  have hef : ∀ i j, star (e i) ⬝ᵥ f j = 0 := by
    intro i j; simp only [he, hf, inner_vecOf, embed_ct_mul_flag, trace_zero, zero_div]
  have hfe : ∀ i j, star (f j) ⬝ᵥ e i = 0 := by
    intro i j; simp only [he, hf, inner_vecOf, flag_ct_mul_embed, trace_zero, zero_div]
  -- the output operator
  set a : ι → ℝ := fun i => (1 - ℓ) * p i with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => mul_nonneg (by linarith) (hp i)
  have hX : ampliate (noisyChannel U p ℓ) n (ketbra (omega n)) -
      ampliate (idealChannel (U i₀)) n (ketbra (omega n)) =
      (∑ i, ((a i : ℝ) : ℂ) • ketbra (e i) + ∑ j, ((ℓ : ℝ) : ℂ) • ketbra (f j)) -
        ketbra (e i₀) := by
    rw [noisyChannel, idealChannel, ampliate_krausMap, ampliate_krausMap, krausMap_ketbra,
      krausMap_ketbra, Fintype.sum_unique (ι := Unit), Fintype.sum_sum_type]
    congr 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      change ketbra (vecOf _) = _
      rw [noiseKraus, Sum.elim_inl, vecOf_smul, ketbra_real_smul, Real.sq_sqrt (ha0 i)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      change ketbra (vecOf _) = _
      rw [noiseKraus, Sum.elim_inr, vecOf_smul, ketbra_real_smul, Real.sq_sqrt hℓ0]
  rw [hX]
  have hsumf : ∑ j : n, ℓ * (1 / (Fintype.card n : ℝ)) = ℓ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have hsuma : ∑ i ∈ Finset.univ.erase i₀, a i = (1 - ℓ) * (1 - p i₀) := by
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ _), hsum]
  apply le_antisymm
  · -- upper bound: triangle inequality
    have hsplit : (∑ i, ((a i : ℝ) : ℂ) • ketbra (e i) + ∑ j, ((ℓ : ℝ) : ℂ) • ketbra (f j)) -
        ketbra (e i₀) = -((((1 - a i₀) : ℝ) : ℂ) • ketbra (e i₀)) +
          ∑ i ∈ Finset.univ.erase i₀, ((a i : ℝ) : ℂ) • ketbra (e i) +
          ∑ j, ((ℓ : ℝ) : ℂ) • ketbra (f j) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      push_cast
      rw [sub_smul, one_smul]; abel
    rw [hsplit]
    have hH : ∀ (r : ℝ) (v : (n ⊕ Unit) × n → ℂ), ((r : ℂ) • ketbra v).IsHermitian := by
      intro r v
      rw [IsHermitian, conjTranspose_smul, (ketbra_posSemidef v).1.eq, Complex.star_def,
        Complex.conj_ofReal]
    have hS1 : (∑ i ∈ Finset.univ.erase i₀, ((a i : ℝ) : ℂ) • ketbra (e i)).IsHermitian := by
      refine isSelfAdjoint_sum _ fun i _ => hH _ _
    have hS2 : (∑ j, ((ℓ : ℝ) : ℂ) • ketbra (f j)).IsHermitian :=
      isSelfAdjoint_sum _ fun j _ => hH _ _
    have h1 : 0 ≤ 1 - a i₀ := by
      have : p i₀ ≤ 1 := by
        rw [← hsum]; exact Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ _)
      simp only [ha]; nlinarith
    have b1 := traceNorm_add_le ((hH (1 - a i₀) (e i₀)).neg.add hS1) hS2
    have b2 := traceNorm_add_le (hH (1 - a i₀) (e i₀)).neg hS1
    have b3 := traceNorm_sum_le (Finset.univ.erase i₀) (fun i => ((a i : ℝ) : ℂ) • ketbra (e i))
      (fun i _ => hH _ _)
    have b4 := traceNorm_sum_le Finset.univ (fun j => ((ℓ : ℝ) : ℂ) • ketbra (f j))
      (fun j _ => hH _ _)
    have vA : traceNorm (-((((1 - a i₀) : ℝ) : ℂ) • ketbra (e i₀))) = 1 - a i₀ := by
      rw [traceNorm_neg, traceNorm_smul_ketbra h1, hee, if_pos rfl, Complex.one_re, mul_one]
    have vS1 : ∑ i ∈ Finset.univ.erase i₀, traceNorm (((a i : ℝ) : ℂ) • ketbra (e i)) =
        (1 - ℓ) * (1 - p i₀) := by
      rw [← hsuma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [traceNorm_smul_ketbra (ha0 i), hee, if_pos rfl, Complex.one_re, mul_one]
    have vS2 : ∑ j, traceNorm (((ℓ : ℝ) : ℂ) • ketbra (f j)) = ℓ := by
      have : ∀ j, traceNorm (((ℓ : ℝ) : ℂ) • ketbra (f j)) = ℓ * (1 / (Fintype.card n : ℝ)) :=
        fun j => by rw [traceNorm_smul_ketbra hℓ0, hff, Complex.ofReal_re]
      rw [Finset.sum_congr rfl fun j _ => this j, hsumf]
    simp only [ha] at vA b1 b2 ⊢
    linarith
  · -- lower bound: Helstrom test with the projector `1 - |ψ₀⟩⟨ψ₀|`
    set Y := (∑ i, ((a i : ℝ) : ℂ) • ketbra (e i) + ∑ j, ((ℓ : ℝ) : ℂ) • ketbra (f j)) -
      ketbra (e i₀) with hYdef
    have hH : ∀ (r : ℝ) (v : (n ⊕ Unit) × n → ℂ), ((r : ℂ) • ketbra v).IsHermitian := by
      intro r v
      rw [IsHermitian, conjTranspose_smul, (ketbra_posSemidef v).1.eq, Complex.star_def,
        Complex.conj_ofReal]
    have hY : Y.IsHermitian :=
      ((isSelfAdjoint_sum _ fun i _ => hH _ _).add (isSelfAdjoint_sum _ fun j _ => hH _ _)).sub
        (ketbra_posSemidef _).1
    have he0 : star (e i₀) ⬝ᵥ e i₀ = 1 := by rw [hee, if_pos rfl]
    have hP := (ketbra_isProjector he0).one_sub
    have h := (traceNorm_isGreatest hY).2 ⟨1 - ketbra (e i₀), hP, rfl⟩
    have hsumC : ∑ i, ((a i : ℝ) : ℂ) = ((1 - ℓ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum, ha, ← Finset.mul_sum, hsum, mul_one]
    have hsumfC : ∑ j : n, (ℓ : ℂ) * (((1 / (Fintype.card n : ℝ)) : ℝ) : ℂ) = (ℓ : ℂ) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hsumf
      push_cast at this ⊢; exact this
    have tY : trace Y = 0 := by
      simp only [hYdef, trace_sub, trace_add, trace_sum, trace_smul, trace_ketbra, hee, hff,
        if_pos rfl, smul_eq_mul, mul_one, hsumfC]
      push_cast
      have h' := hsumC; push_cast at h'
      simp only [mul_one] at h' ⊢; linear_combination h'
    have tQY : trace (ketbra (e i₀) * Y) = ((a i₀ - 1 : ℝ) : ℂ) := by
      simp only [hYdef, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul,
        trace_sub, trace_add, trace_sum, trace_smul, trace_ketbra_mul_ketbra, hee, hef, hfe,
        smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
        ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_pos rfl]
      rw [Finset.sum_eq_single i₀ (fun b _ hb => by simp [hb]) (by simp)]
      simp
    have key : (trace ((1 - ketbra (e i₀)) * Y) - trace ((1 - (1 - ketbra (e i₀))) * Y)).re =
        2 * (1 - (1 - ℓ) * p i₀) := by
      rw [sub_sub_cancel, Matrix.sub_mul, Matrix.one_mul, trace_sub, tY, tQY]
      simp only [ha]; simp; ring
    rw [← key]; exact h

/-! ### Block form of the channels -/

theorem noisyChannel_apply (U : ι → Matrix n n ℂ) (p : ι → ℝ) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ)
    (hℓ1 : ℓ ≤ 1) (hp : ∀ i, 0 ≤ p i) (ρ : Matrix n n ℂ) :
    noisyChannel U p ℓ ρ = Matrix.fromBlocks
      (∑ i, (((1 - ℓ) * p i : ℝ) : ℂ) • (U i * ρ * (U i)ᴴ)) 0 0
      (Matrix.of fun _ _ => (ℓ : ℂ) * trace ρ) := by
  have hsq : ∀ s : ℝ, 0 ≤ s → ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) = (s : ℂ) := by
    intro s hs; rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs]
  have hsq' : ∀ i, ((Real.sqrt ((1 - ℓ) * p i) : ℝ) : ℂ) * ((Real.sqrt ((1 - ℓ) * p i) : ℝ) : ℂ)
      = (((1 - ℓ) * p i : ℝ) : ℂ) := fun i => hsq _ (mul_nonneg (by linarith) (hp i))
  ext x y
  rcases x with s | u <;> rcases y with s' | u'
  all_goals
    simp only [noisyChannel, krausMap, noiseKraus, Fintype.sum_sum_type, Matrix.add_apply,
      Matrix.sum_apply, Sum.elim_inl, Sum.elim_inr, Matrix.smul_mul, Matrix.mul_smul,
      conjTranspose_smul, Matrix.smul_apply, smul_eq_mul, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, of_apply, Complex.star_def,
      Complex.conj_ofReal]
  · have h2 : ∀ j, (flagOp j * ρ * (flagOp j)ᴴ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) (Sum.inl s) (Sum.inl s') = 0 := by
      intro j; simp [Matrix.mul_apply, flagOp, Fintype.sum_sum_type]
    have h1 : ∀ i, (embed (U i) * ρ * (embed (U i))ᴴ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) (Sum.inl s) (Sum.inl s') =
        (U i * ρ * (U i)ᴴ) s s' := by
      intro i; simp [Matrix.mul_apply, embed, Fintype.sum_sum_type]
    simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero, ← mul_assoc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm _ ((Real.sqrt _ : ℝ) : ℂ), hsq']
  · simp [Matrix.mul_apply, embed, flagOp, Fintype.sum_sum_type]
  · simp [Matrix.mul_apply, embed, flagOp, Fintype.sum_sum_type]
  · have h1 : ∀ i, (embed (U i) * ρ * (embed (U i))ᴴ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) (Sum.inr u) (Sum.inr u') = 0 := by
      intro i; simp [Matrix.mul_apply, embed, Fintype.sum_sum_type]
    have h2 : ∀ j, (flagOp j * ρ * (flagOp j)ᴴ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) (Sum.inr u) (Sum.inr u') = ρ j j := by
      intro j; simp [Matrix.mul_apply, flagOp, Fintype.sum_sum_type]
    simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add, ← mul_assoc]
    rw [mul_comm _ ((Real.sqrt ℓ : ℝ) : ℂ), hsq ℓ hℓ0, ← Finset.mul_sum]
    rfl

theorem idealChannel_apply (U₀ ρ : Matrix n n ℂ) :
    idealChannel U₀ ρ = Matrix.fromBlocks (U₀ * ρ * U₀ᴴ) 0 0 0 := by
  ext x y
  rcases x with s | u <;> rcases y with s' | u' <;>
    simp [idealChannel, krausMap, Matrix.mul_apply, embed, Fintype.sum_sum_type]

/-! ### Diamond distance (state-input version) and the lower bound -/

lemma omega_norm [Nonempty n] : star (omega n) ⬝ᵥ omega n = 1 := by
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  simp only [dotProduct, Pi.star_apply, omega, Fintype.sum_prod_type, apply_ite star, star_zero,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_pos rfl,
    Finset.sum_ite_eq', Complex.star_def, Complex.conj_ofReal]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt hd.le]
  push_cast
  field_simp

/-- The state-input diamond distance
`sup { ‖(Φ ⊗ id_n)(ρ) − (Ψ ⊗ id_n)(ρ)‖₁ : ρ density matrix on n × n }`
(ancilla of the same dimension as the input). -/
noncomputable def diamondDist {m : Type} [Fintype m] [DecidableEq m]
    (Φ Ψ : Matrix n n ℂ → Matrix m m ℂ) : ℝ :=
  sSup {r : ℝ | ∃ ρ : Matrix (n × n) (n × n) ℂ, ρ.PosSemidef ∧ trace ρ = 1 ∧
    r = traceNorm (ampliate Φ n ρ - ampliate Ψ n ρ)}

lemma traceNorm_sub_channels_le_two {m : Type} [Fintype m] [DecidableEq m]
    {Φ Ψ : Matrix n n ℂ → Matrix m m ℂ} (hΦ : IsKrausChannel Φ) (hΨ : IsKrausChannel Ψ)
    {ρ : Matrix (n × n) (n × n) ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    traceNorm (ampliate Φ n ρ - ampliate Ψ n ρ) ≤ 2 := by
  obtain ⟨h1, t1⟩ := (hΦ.tensorId (k := n)).density hρ htr
  obtain ⟨h2, t2⟩ := (hΨ.tensorId (k := n)).density hρ htr
  calc _ ≤ traceNorm (ampliate Φ n ρ) + traceNorm (ampliate Ψ n ρ) := traceNorm_sub_le h1.1 h2.1
    _ = 2 := by rw [traceNorm_density h1 t1, traceNorm_density h2 t2]; norm_num

theorem le_diamondDist {m : Type} [Fintype m] [DecidableEq m]
    {Φ Ψ : Matrix n n ℂ → Matrix m m ℂ} (hΦ : IsKrausChannel Φ) (hΨ : IsKrausChannel Ψ)
    {ρ : Matrix (n × n) (n × n) ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    traceNorm (ampliate Φ n ρ - ampliate Ψ n ρ) ≤ diamondDist Φ Ψ := by
  refine le_csSup ⟨2, ?_⟩ ⟨ρ, hρ, htr, rfl⟩
  rintro r ⟨σ, hσ, hσt, rfl⟩
  exact traceNorm_sub_channels_le_two hΦ hΨ hσ hσt

theorem diamondDist_le_two [Nonempty n] {m : Type} [Fintype m] [DecidableEq m]
    {Φ Ψ : Matrix n n ℂ → Matrix m m ℂ} (hΦ : IsKrausChannel Φ) (hΨ : IsKrausChannel Ψ) :
    diamondDist Φ Ψ ≤ 2 := by
  refine csSup_le ⟨_, ketbra (omega n), ketbra_posSemidef _, by rw [trace_ketbra, omega_norm],
    rfl⟩ ?_
  rintro r ⟨σ, hσ, hσt, rfl⟩
  exact traceNorm_sub_channels_le_two hΦ hΨ hσ hσt

/-- **Lower bound in the orthogonal-noise diamond formula**:
`2 (1 − (1 − ℓ) p_{i₀}) ≤ ‖E − V₀‖◇` (state-input diamond distance). -/
theorem diamondDist_noisy_ideal_ge [Nonempty n] {U : ι → Matrix n n ℂ}
    (hU : ∀ i, U i ∈ unitaryGroup n ℂ) (hHS : ∀ i j, i ≠ j → trace ((U i)ᴴ * U j) = 0)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1)
    (i₀ : ι) :
    2 * (1 - (1 - ℓ) * p i₀) ≤ diamondDist (noisyChannel U p ℓ) (idealChannel (U i₀)) := by
  rw [← traceNorm_noisy_sub_ideal_maxEnt hU hHS hp hsum hℓ0 hℓ1 i₀]
  exact le_diamondDist (noisyChannel_isKraus hU hp hsum hℓ0 hℓ1) (idealChannel_isKraus (hU i₀))
    (ketbra_posSemidef _) (by rw [trace_ketbra, omega_norm])
