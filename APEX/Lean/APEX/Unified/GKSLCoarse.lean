import APEX.Unified.Duhamel
import APEX.Quantum.CPTP
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A concrete GKSL coarse-graining: two qubits, partial trace, computed defect

Everything here is computed, not assumed (except the stated hypotheses `γ ≥ 0`, `H` Hermitian,
`g` real).

## Coarse-graining
* `ptr : M_{m⊗k}(ℂ) →ₗ[ℂ] M_m(ℂ)`, `(ptr X)_{ij} = Σ_a X_{(i,a),(j,a)}` (partial trace over the
  second factor); `trace_ptr` (trace preserving); `ptr_eq_krausMap` / `ptrKraus_sum` (Kraus form
  with `K_a = 1 ⊗ ⟨a|`, `Σ K_aᴴ K_a = 1`); `ptr_isKrausChannel` (so it is CPTP in the sense of
  `APEX.Quantum.IsKrausChannel`, incl. complete positivity); `ptr_posSemidef`.
* Local generators: `liftL Φ = Φ ⊗ id`, `liftR Ψ = id ⊗ Ψ` (blockwise). `ptr_liftL`:
  `tr₂ ∘ (Φ ⊗ id) = Φ ∘ tr₂` (any linear `Φ`); `ptr_liftR`: `tr₂ ∘ (id ⊗ Ψ) = 0` if
  `tr Ψ(Y) = 0` for all `Y`.
* Generators: `ham H ρ = −i[H,ρ]`, `deph γ U ρ = γ(UρU − ρ)`; both trace-annihilating
  (`trace_ham`, `trace_deph` for `U² = 1`). Pauli `σz`, `σx`.

## Two-qubit model (`M_4 = M_{Fin 2 × Fin 2}`)
* `L1 γ H = deph γ σz + ham H` on one qubit, `L0 = L1 γ₁ H₁ ⊗ id + id ⊗ L1 γ₂ H₂`,
  `Lint g = −i[g Z⊗X, ·]`.
* `ptr_L0`: exact intertwining `tr₂ ∘ L0 = L1 γ₁ H₁ ∘ tr₂` (zero defect), and `ptr_exp_L0`:
  `R e^{t L0} = e^{t L1} R` for all real `t` (via `APEX.Unified.comp_exp_iff`).
* `defect_eq`: `tr₂ ∘ (L0 + Lint g) − L1 ∘ tr₂ = tr₂ ∘ Lint g`, and `ptr_Lint_apply`: explicitly,
  `tr₂(Lint g ρ) = [[0, −2ig(ρ_{01,10} + ρ_{00,11})], [2ig(ρ_{11,00} + ρ_{10,01}), 0]]`.
* Norms: Hilbert–Schmidt, via `hs : M_n(ℂ) ≃ₗ EuclideanSpace ℂ (n × n)`, and `sup Φ` the
  transported real-linear bounded operator; `inner_hs : ⟪hs X, hs Y⟫ = tr(Xᴴ Y)`.
* `norm_defect_le`: `‖sup (tr₂ ∘ Lint g)‖ ≤ 2√2 |g|` (HS operator norm).
* Contractivity is **derived**: `norm_exp_le_one_of_dissipative` (if `Re⟪x, Lx⟫ ≤ 0` on a complex
  Hilbert space then `‖e^{tL}‖ ≤ 1`, `t ≥ 0`); `ham_dissipative` (Hermitian `H`),
  `deph_dissipative` (`γ ≥ 0`, `U` Hermitian, `U² = 1`), closure under `+`, `liftL`, `liftR`;
  hence `L1_dissipative`, `Ltot_dissipative`.
* **`norm_ptr_exp_sub_le`**: for `γ₁, γ₂ ≥ 0`, Hermitian `H₁, H₂`, real `g`, `t ≥ 0`:
  `‖R e^{t(L0 + Lint g)} − e^{t L1} R‖_{HS→HS} ≤ t · 2√2 |g|`.

## Counter-model (exact consistency is a nontrivial constraint)
* `defect_lower_bound`: for *every* bounded real-linear `T` on the coarse HS space,
  `‖R ∘ (L0 + Lint g) − T ∘ R‖ ≥ 2|g|` (witness `ρ₀ = |00⟩⟨11|`, which has `tr₂ ρ₀ = 0`
  but `tr₂(Lint g ρ₀) ≠ 0`).
* `no_exact_coarse_generator`: for `g ≠ 0` there is no bounded `A'` with
  `R e^{t(L0+Lint g)} = e^{tA'} R` for all `t`, although `R = tr₂` is CPTP.

## Caveats
* The norm is Hilbert–Schmidt, not the trace norm natural for states; the bounds are
  operator-norm bounds on the HS space. HS-contractivity holds here because the generators are
  Hamiltonian plus Hermitian-unitary dephasing; general GKSL semigroups need not be HS-contractive.
* No complete positivity of `e^{tL}` is proved here (only of `R`); the GKSL form is used only
  through the explicit generators above.
* Scale consistency (small defect) is a consistency/approximation property of a pair of models,
  not by itself a physical law.
-/

open Matrix
open scoped ComplexOrder Kronecker

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace APEX.Unified.GKSLCoarse

section PartialTrace
variable {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-- Partial trace over the second tensor factor: `(ptr X)_{ij} = Σ_a X_{(i,a),(j,a)}`. -/
def ptr : Matrix (m × k) (m × k) ℂ →ₗ[ℂ] Matrix m m ℂ where
  toFun X := Matrix.of fun i j => ∑ a, X (i, a) (j, a)
  map_add' X Y := by ext i j; simp [Finset.sum_add_distrib]
  map_smul' c X := by ext i j; simp [Finset.mul_sum]

@[simp] theorem ptr_apply (X : Matrix (m × k) (m × k) ℂ) (i j : m) :
    ptr X i j = ∑ a, X (i, a) (j, a) := rfl

theorem trace_ptr (X : Matrix (m × k) (m × k) ℂ) : trace (ptr X) = trace X := by
  simp [Matrix.trace, Fintype.sum_prod_type]

/-- Kraus operators of the partial trace: `K_a = 1 ⊗ ⟨a|`. -/
def ptrKraus (a : k) : Matrix m (m × k) ℂ := fun i p => if p = (i, a) then 1 else 0

theorem ptrKraus_sum : ∑ a, (ptrKraus (m := m) (k := k) a)ᴴ * ptrKraus a = 1 := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, ptrKraus]
  rcases p with ⟨j, b⟩; rcases q with ⟨j', b'⟩
  simp only [Prod.mk.injEq, apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero,
    ite_and]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : j = j' <;> by_cases h2 : b = b' <;> simp [h1, h2, eq_comm]

theorem ptr_eq_krausMap (X : Matrix (m × k) (m × k) ℂ) :
    ptr X = APEX.Quantum.krausMap (ptrKraus (m := m) (k := k)) X := by
  ext i j
  simp only [APEX.Quantum.krausMap, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply,
    ptrKraus, ptr_apply]
  apply Finset.sum_congr rfl; intro a _
  simp [apply_ite star, Finset.sum_ite_eq', ite_mul, mul_ite]

/-- The partial trace is a quantum channel (Kraus form with `Σ K_aᴴ K_a = 1`); hence it is
trace preserving, positive, and completely positive (`APEX.Quantum.IsKrausChannel.*`). -/
theorem ptr_isKrausChannel :
    APEX.Quantum.IsKrausChannel (fun X : Matrix (m × k) (m × k) ℂ => ptr X) :=
  ⟨k, inferInstance, ptrKraus, ptrKraus_sum, funext ptr_eq_krausMap⟩

theorem ptr_posSemidef {X : Matrix (m × k) (m × k) ℂ} (hX : X.PosSemidef) : (ptr X).PosSemidef :=
  ptr_isKrausChannel.posSemidef_apply hX


/-! ### Local generators `Φ ⊗ id` and `id ⊗ Ψ` -/

/-- `(Φ ⊗ id)(X)`, blockwise: `(Φ ⊗ id)(X)_{(i,a),(j,b)} = Φ(X_{(·,a),(·,b)})_{ij}`. -/
def liftL (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ) :
    Matrix (m × k) (m × k) ℂ →ₗ[ℂ] Matrix (m × k) (m × k) ℂ where
  toFun X := Matrix.of fun p q => Φ (X.submatrix (fun i => (i, p.2)) (fun j => (j, q.2))) p.1 q.1
  map_add' X Y := by ext p q; simp [Matrix.submatrix_add]
  map_smul' c X := by ext p q; simp [Matrix.submatrix_smul]

/-- `(id ⊗ Ψ)(X)`, blockwise: `(id ⊗ Ψ)(X)_{(i,a),(j,b)} = Ψ(X_{(i,·),(j,·)})_{ab}`. -/
def liftR (Ψ : Matrix k k ℂ →ₗ[ℂ] Matrix k k ℂ) :
    Matrix (m × k) (m × k) ℂ →ₗ[ℂ] Matrix (m × k) (m × k) ℂ where
  toFun X := Matrix.of fun p q => Ψ (X.submatrix (fun a => (p.1, a)) (fun b => (q.1, b))) p.2 q.2
  map_add' X Y := by ext p q; simp [Matrix.submatrix_add]
  map_smul' c X := by ext p q; simp [Matrix.submatrix_smul]

@[simp] theorem liftL_apply (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix (m × k) (m × k) ℂ)
    (p q : m × k) :
    liftL Φ X p q = Φ (X.submatrix (fun i => (i, p.2)) (fun j => (j, q.2))) p.1 q.1 := rfl

@[simp] theorem liftR_apply (Ψ : Matrix k k ℂ →ₗ[ℂ] Matrix k k ℂ) (X : Matrix (m × k) (m × k) ℂ)
    (p q : m × k) :
    liftR Ψ X p q = Ψ (X.submatrix (fun a => (p.1, a)) (fun b => (q.1, b))) p.2 q.2 := rfl

theorem ptr_eq_sum_blocks (X : Matrix (m × k) (m × k) ℂ) :
    ptr X = ∑ a, X.submatrix (fun i => (i, a)) (fun j => (j, a)) := by
  ext i j; simp [Matrix.sum_apply]

/-- `tr₂ ∘ (Φ ⊗ id) = Φ ∘ tr₂` for every linear `Φ`. -/
theorem ptr_liftL (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ) :
    ptr ∘ₗ liftL (k := k) Φ = Φ ∘ₗ ptr := by
  apply LinearMap.ext; intro X
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ptr_eq_sum_blocks X, map_sum]
  ext i j; simp [Matrix.sum_apply]

/-- `tr₂ ∘ (id ⊗ Ψ) = 0` whenever `Ψ` is trace-annihilating (`tr Ψ(Y) = 0`), as every GKSL
generator is. -/
theorem ptr_liftR (Ψ : Matrix k k ℂ →ₗ[ℂ] Matrix k k ℂ) (hΨ : ∀ Y, trace (Ψ Y) = 0) :
    ptr ∘ₗ liftR (m := m) Ψ = 0 := by
  apply LinearMap.ext; intro X
  ext i j
  have := hΨ (X.submatrix (fun a => (i, a)) (fun b => (j, b)))
  simpa [Matrix.trace] using this

end PartialTrace

section Generators
variable {n : Type} [Fintype n] [DecidableEq n]

/-- Hamiltonian generator `ρ ↦ −i [H, ρ]`. -/
def ham (H : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun ρ := (-Complex.I) • (H * ρ - ρ * H)
  map_add' X Y := by
    rw [Matrix.mul_add, Matrix.add_mul, ← smul_add]; congr 1; abel
  map_smul' c X := by simp [smul_sub, smul_comm c]

/-- Dephasing-type generator `ρ ↦ γ (U ρ U − ρ)` (for `U = Z` this is Pauli-`Z` dephasing). -/
def deph (γ : ℝ) (U : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun ρ := (γ : ℂ) • (U * ρ * U - ρ)
  map_add' X Y := by
    rw [Matrix.mul_add, Matrix.add_mul, ← smul_add]; congr 1; abel
  map_smul' c X := by simp [smul_sub, smul_comm c]

@[simp] theorem ham_apply (H ρ : Matrix n n ℂ) : ham H ρ = (-Complex.I) • (H * ρ - ρ * H) := rfl
@[simp] theorem deph_apply (γ : ℝ) (U ρ : Matrix n n ℂ) :
    deph γ U ρ = (γ : ℂ) • (U * ρ * U - ρ) := rfl

theorem trace_ham (H ρ : Matrix n n ℂ) : trace (ham H ρ) = 0 := by
  simp [trace_sub, trace_mul_comm H ρ]

theorem trace_deph (γ : ℝ) {U : Matrix n n ℂ} (hU : U * U = 1) (ρ : Matrix n n ℂ) :
    trace (deph γ U ρ) = 0 := by
  have : trace (U * ρ * U) = trace ρ := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  simp [trace_sub, this]

/-- Pauli matrices. -/
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem σz_mul_self : σz * σz = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σz, Matrix.mul_apply, Fin.sum_univ_two]

end Generators


section HS
/-! ### Hilbert–Schmidt encoding `M_n(ℂ) ≅ EuclideanSpace ℂ (n × n)` -/
variable {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype n''] [DecidableEq n'']

/-- `X ↦ (X_{ij})_{(i,j)}`; the Euclidean norm of `hs X` is the Hilbert–Schmidt norm of `X`. -/
def hs : Matrix n n ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (n × n) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun v := Matrix.of fun i j => v (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem hs_apply (X : Matrix n n ℂ) (p : n × n) : hs X p = X p.1 p.2 := rfl
@[simp] theorem hs_symm_apply (v : EuclideanSpace ℂ (n × n)) (i j : n) :
    hs.symm v i j = v (i, j) := rfl

theorem inner_hs (X Y : Matrix n n ℂ) : inner ℂ (hs X) (hs Y) = trace (Xᴴ * Y) := by
  simp only [PiLp.inner_apply, hs_apply, RCLike.inner_apply', Matrix.trace, Matrix.diag,
    Matrix.mul_apply, conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]; rfl

theorem norm_hs_sq (X : Matrix n n ℂ) : ‖hs X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]; rfl

/-- A linear superoperator transported to the Hilbert–Schmidt spaces, as a real-linear bounded
operator (the setting of `APEX.Unified.Duhamel`). -/
noncomputable def sup (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ) :
    EuclideanSpace ℂ (n × n) →L[ℝ] EuclideanSpace ℂ (n' × n') :=
  (LinearMap.toContinuousLinearMap (hs.toLinearMap ∘ₗ Φ ∘ₗ hs.symm.toLinearMap)).restrictScalars ℝ

@[simp] theorem sup_apply (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ) (v : EuclideanSpace ℂ (n × n)) :
    sup Φ v = hs (Φ (hs.symm v)) := rfl

theorem sup_comp (Φ : Matrix n' n' ℂ →ₗ[ℂ] Matrix n'' n'' ℂ) (Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ) :
    sup (Φ ∘ₗ Ψ) = (sup Φ).comp (sup Ψ) := by
  ext v; simp

theorem sup_add (Φ Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ) : sup (Φ + Ψ) = sup Φ + sup Ψ := by
  ext v; simp

theorem sup_sub (Φ Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ) : sup (Φ - Ψ) = sup Φ - sup Ψ := by
  ext v; simp

end HS

section Dissipative
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Dissipativity ⇒ contractivity** (bounded Lumer–Phillips, easy direction): if
`Re ⟪x, L x⟫ ≤ 0` for all `x`, then `‖e^{tL}‖ ≤ 1` for all `t ≥ 0`. -/
theorem norm_exp_le_one_of_dissipative (L : H →L[ℝ] H)
    (hL : ∀ x, RCLike.re (inner ℂ x (L x)) ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • L)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  let y : ℝ → H := fun s => NormedSpace.exp (s • L) x
  have hy : ∀ s, HasDerivAt y (L (y s)) s := by
    intro s
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) L s
    have := h.clm_apply (hasDerivAt_const s x)
    simpa [y] using this
  let f : ℝ → ℝ := fun s => RCLike.re (inner ℂ (y s) (y s))
  have hf : ∀ s, HasDerivAt f (RCLike.re (inner ℂ (y s) (L (y s)) + inner ℂ (L (y s)) (y s))) s := by
    intro s
    have h := HasDerivAt.inner ℂ (hy s) (hy s)
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h)
  have hneg : ∀ s, RCLike.re (inner ℂ (y s) (L (y s)) + inner ℂ (L (y s)) (y s)) ≤ 0 := by
    intro s
    rw [map_add, ← inner_conj_symm (L (y s)) (y s), RCLike.conj_re]
    linarith [hL (y s)]
  have hanti : Antitone f := antitone_of_hasDerivAt_nonpos hf hneg
  have h0 : f t ≤ f 0 := hanti ht
  have e : ∀ s, f s = ‖y s‖ ^ 2 := fun s => by
    simp only [f]; rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [e, e] at h0
  have hy0 : y 0 = x := by simp [y]
  rw [hy0] at h0
  rw [one_mul]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h0

end Dissipative

section MatrixDissipative
variable {n : Type} [Fintype n] [DecidableEq n]

/-- Hilbert–Schmidt dissipativity of a superoperator: `Re tr(Xᴴ Φ(X)) ≤ 0` for all `X`. -/
def HSDissipative (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∀ X : Matrix n n ℂ, (trace (Xᴴ * Φ X)).re ≤ 0

theorem HSDissipative.add {Φ Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hΦ : HSDissipative Φ)
    (hΨ : HSDissipative Ψ) : HSDissipative (Φ + Ψ) := by
  intro X
  have h1 := hΦ X; have h2 := hΨ X
  simp only [LinearMap.add_apply, Matrix.mul_add, trace_add, Complex.add_re]
  linarith

theorem HSDissipative.contractive {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hΦ : HSDissipative Φ)
    {t : ℝ} (ht : 0 ≤ t) : ‖NormedSpace.exp (t • sup Φ)‖ ≤ 1 := by
  refine norm_exp_le_one_of_dissipative (sup Φ) (fun v => ?_) ht
  have h := hΦ (hs.symm v)
  have e : inner ℂ v (sup Φ v) = trace ((hs.symm v)ᴴ * Φ (hs.symm v)) := by
    rw [sup_apply, ← inner_hs]; rfl
  rw [e]; exact h

lemma trace_conj_mul_self_re (X : Matrix n n ℂ) : (trace (Xᴴ * X)).re = ‖hs X‖ ^ 2 := by
  rw [← inner_hs, inner_self_eq_norm_sq_to_K]; norm_cast

theorem ham_dissipative {H : Matrix n n ℂ} (hH : H.IsHermitian) : HSDissipative (ham H) := by
  intro X
  have ha : star (trace (Xᴴ * (H * X))) = trace (Xᴴ * (H * X)) := by
    rw [← trace_conjTranspose]; simp [conjTranspose_mul, hH.eq, Matrix.mul_assoc]
  have hb : star (trace (Xᴴ * (X * H))) = trace (Xᴴ * (X * H)) := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, hH.eq,
      conjTranspose_conjTranspose, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  have ha' := Complex.conj_eq_iff_im.1 ha
  have hb' := Complex.conj_eq_iff_im.1 hb
  simp only [ham_apply, Matrix.mul_smul, trace_smul, Matrix.mul_sub, trace_sub, smul_eq_mul,
    Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im, Complex.sub_im]
  rw [ha', hb']; simp

theorem deph_dissipative {γ : ℝ} (hγ : 0 ≤ γ) {U : Matrix n n ℂ} (hU : U.IsHermitian)
    (hUU : U * U = 1) : HSDissipative (deph γ U) := by
  intro X
  have hiso : ‖hs (U * X * U)‖ = ‖hs X‖ := by
    have e1 : (U * X * U)ᴴ * (U * X * U) = U * (Xᴴ * X) * U := by
      rw [conjTranspose_mul, conjTranspose_mul, hU.eq]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U U, hUU, Matrix.one_mul]
    have : trace ((U * X * U)ᴴ * (U * X * U)) = trace (Xᴴ * X) := by
      rw [e1, trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    have h2 := trace_conj_mul_self_re (U * X * U)
    rw [this, trace_conj_mul_self_re] at h2
    exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2).symm
  have hcs : (trace (Xᴴ * (U * X * U))).re ≤ ‖hs X‖ ^ 2 := by
    have h := re_inner_le_norm (𝕜 := ℂ) (hs X) (hs (U * X * U))
    rw [hiso, ← sq] at h
    rw [← inner_hs]; exact h
  simp only [deph_apply, Matrix.mul_smul, trace_smul, Matrix.mul_sub, trace_sub, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]
  rw [trace_conj_mul_self_re]
  nlinarith

end MatrixDissipative

section LiftDissipative
variable {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

theorem trace_liftL (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix (m × k) (m × k) ℂ) :
    trace (Xᴴ * liftL Φ X) = ∑ a, ∑ b, trace ((X.submatrix (fun i => (i, a)) (fun j => (j, b)))ᴴ *
      Φ (X.submatrix (fun i => (i, a)) (fun j => (j, b)))) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, liftL_apply,
    Fintype.sum_prod_type, Matrix.submatrix_apply]
  conv_lhs => enter [2, j, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]

theorem trace_liftR (Ψ : Matrix k k ℂ →ₗ[ℂ] Matrix k k ℂ) (X : Matrix (m × k) (m × k) ℂ) :
    trace (Xᴴ * liftR Ψ X) = ∑ i, ∑ j, trace ((X.submatrix (fun a => (i, a)) (fun b => (j, b)))ᴴ *
      Ψ (X.submatrix (fun a => (i, a)) (fun b => (j, b)))) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, liftR_apply,
    Fintype.sum_prod_type, Matrix.submatrix_apply]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem HSDissipative.liftL {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ} (hΦ : HSDissipative Φ) :
    HSDissipative (liftL (k := k) Φ) := by
  intro X
  rw [trace_liftL, Complex.re_sum]
  exact Finset.sum_nonpos fun a _ => by
    rw [Complex.re_sum]; exact Finset.sum_nonpos fun b _ => hΦ _

theorem HSDissipative.liftR {Ψ : Matrix k k ℂ →ₗ[ℂ] Matrix k k ℂ} (hΨ : HSDissipative Ψ) :
    HSDissipative (liftR (m := m) Ψ) := by
  intro X
  rw [trace_liftR, Complex.re_sum]
  exact Finset.sum_nonpos fun a _ => by
    rw [Complex.re_sum]; exact Finset.sum_nonpos fun b _ => hΨ _

end LiftDissipative

section TwoQubit
/-! ### The concrete two-qubit model -/

/-- Single-qubit GKSL generator: `Z`-dephasing at rate `γ` plus Hamiltonian `H`. -/
noncomputable def L1 (γ : ℝ) (H : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  deph γ σz + ham H

/-- Non-interacting two-qubit generator `L₁ ⊗ id + id ⊗ L₂`. -/
noncomputable def L0 (γ₁ : ℝ) (H₁ : Matrix (Fin 2) (Fin 2) ℂ) (γ₂ : ℝ)
    (H₂ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  liftL (L1 γ₁ H₁) + liftR (L1 γ₂ H₂)

/-- Interaction `ρ ↦ −i [g Z⊗X, ρ]`. -/
noncomputable def Lint (g : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ham ((g : ℂ) • (σz ⊗ₖ σx))

theorem trace_L1 (γ : ℝ) (H ρ : Matrix (Fin 2) (Fin 2) ℂ) : trace (L1 γ H ρ) = 0 := by
  rw [L1, LinearMap.add_apply, trace_add, trace_deph γ σz_mul_self, trace_ham, add_zero]

/-- **Exact intertwining** for the non-interacting generator: `tr₂ ∘ L0 = L₁ ∘ tr₂`. -/
theorem ptr_L0 (γ₁ : ℝ) (H₁ : Matrix (Fin 2) (Fin 2) ℂ) (γ₂ : ℝ) (H₂ : Matrix (Fin 2) (Fin 2) ℂ) :
    ptr ∘ₗ L0 γ₁ H₁ γ₂ H₂ = L1 γ₁ H₁ ∘ₗ ptr := by
  rw [L0, LinearMap.comp_add, ptr_liftL, ptr_liftR _ (trace_L1 γ₂ H₂), add_zero]

/-- Hence exact semigroup consistency: `R e^{t L0} = e^{t L₁} R` for all `t` (HS encoding). -/
theorem ptr_exp_L0 (γ₁ : ℝ) (H₁ : Matrix (Fin 2) (Fin 2) ℂ) (γ₂ : ℝ)
    (H₂ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    (sup (ptr (m := Fin 2) (k := Fin 2))).comp (NormedSpace.exp (t • sup (L0 γ₁ H₁ γ₂ H₂))) =
      (NormedSpace.exp (t • sup (L1 γ₁ H₁))).comp (sup ptr) := by
  refine (APEX.Unified.comp_exp_iff _ _ _).2 ?_ t
  rw [← sup_comp, ← sup_comp, ptr_L0]

/-- The defect of the interacting generator is exactly the partial trace of the interaction. -/
theorem defect_eq (γ₁ : ℝ) (H₁ : Matrix (Fin 2) (Fin 2) ℂ) (γ₂ : ℝ)
    (H₂ : Matrix (Fin 2) (Fin 2) ℂ) (g : ℝ) :
    ptr ∘ₗ (L0 γ₁ H₁ γ₂ H₂ + Lint g) - L1 γ₁ H₁ ∘ₗ ptr = ptr ∘ₗ Lint g := by
  rw [LinearMap.comp_add, ptr_L0]; abel

/-- Explicit defect: `tr₂(−i[g Z⊗X, ρ])` has zero diagonal and off-diagonal entries
`∓ 2 i g (ρ_{(0,1),(1,0)} + ρ_{(0,0),(1,1)})`, resp. `(ρ_{(1,1),(0,0)} + ρ_{(1,0),(0,1)})`. -/
theorem ptr_Lint_apply (g : ℝ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ptr (Lint g ρ) = !![0, -(2 * Complex.I * g) * (ρ (0, 1) (1, 0) + ρ (0, 0) (1, 1));
      (2 * Complex.I * g) * (ρ (1, 1) (0, 0) + ρ (1, 0) (0, 1)), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lint, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, σz, σx,
      kroneckerMap_apply] <;> ring

lemma norm_add_sq_le' (z w : ℂ) : ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := norm_add_le z w
  have h0 := norm_nonneg (z + w)
  nlinarith [sq_nonneg (‖z‖ - ‖w‖), norm_nonneg z, norm_nonneg w]

/-- **Defect bound** in the Hilbert–Schmidt operator norm: `‖D‖ ≤ 2√2 |g|`. -/
theorem norm_defect_le (g : ℝ) :
    ‖sup (ptr (m := Fin 2) (k := Fin 2) ∘ₗ Lint g)‖ ≤ 2 * Real.sqrt 2 * |g| := by
  have hc : 0 ≤ 2 * Real.sqrt 2 * |g| := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  set ρ := hs.symm v with hρ
  have hv : v = hs ρ := by simp [hρ]
  have hsq : ‖sup (ptr ∘ₗ Lint g) v‖ ^ 2 ≤ (2 * Real.sqrt 2 * |g| * ‖v‖) ^ 2 := by
    rw [sup_apply, LinearMap.comp_apply, ← hρ, ptr_Lint_apply, norm_hs_sq, hv, mul_pow,
      norm_hs_sq]
    simp only [Fin.sum_univ_two, Fintype.sum_prod_type, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      norm_zero, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat]
    have hs2 : (2 * √2 * |g|) ^ 2 = 8 * g ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), sq_abs]; ring
    rw [hs2]
    simp only [mul_pow, sq_abs, mul_one]
    have e1 := norm_add_sq_le' (ρ (0, 1) (1, 0)) (ρ (0, 0) (1, 1))
    have e2 := norm_add_sq_le' (ρ (1, 1) (0, 0)) (ρ (1, 0) (0, 1))
    have hg : 0 ≤ g ^ 2 := sq_nonneg g
    have f1 := mul_le_mul_of_nonneg_left e1 hg
    have f2 := mul_le_mul_of_nonneg_left e2 hg
    have p : ∀ z : ℂ, 0 ≤ g ^ 2 * ‖z‖ ^ 2 := fun z => mul_nonneg hg (sq_nonneg _)
    nlinarith [p (ρ (0, 0) (0, 0)), p (ρ (0, 0) (0, 1)), p (ρ (0, 0) (1, 0)), p (ρ (0, 1) (0, 0)),
      p (ρ (0, 1) (0, 1)), p (ρ (0, 1) (1, 1)), p (ρ (1, 0) (0, 0)), p (ρ (1, 0) (1, 0)),
      p (ρ (1, 0) (1, 1)), p (ρ (1, 1) (0, 1)), p (ρ (1, 1) (1, 0)), p (ρ (1, 1) (1, 1))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

theorem σz_isHermitian : σz.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σz]

theorem interaction_isHermitian (g : ℝ) : ((g : ℂ) • (σz ⊗ₖ σx)).IsHermitian := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [σz, σx, kroneckerMap_apply]

theorem L1_dissipative {γ : ℝ} (hγ : 0 ≤ γ) {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian) :
    HSDissipative (L1 γ H) :=
  (deph_dissipative hγ σz_isHermitian σz_mul_self).add (ham_dissipative hH)

theorem Ltot_dissipative {γ₁ γ₂ : ℝ} (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    {H₁ H₂ : Matrix (Fin 2) (Fin 2) ℂ} (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) (g : ℝ) :
    HSDissipative (L0 γ₁ H₁ γ₂ H₂ + Lint g) :=
  (((L1_dissipative hγ₁ hH₁).liftL).add ((L1_dissipative hγ₂ hH₂).liftR)).add
    (ham_dissipative (interaction_isHermitian g))

theorem sup_defect_eq (γ₁ : ℝ) (H₁ : Matrix (Fin 2) (Fin 2) ℂ) (γ₂ : ℝ)
    (H₂ : Matrix (Fin 2) (Fin 2) ℂ) (g : ℝ) :
    (sup ptr).comp (sup (L0 γ₁ H₁ γ₂ H₂ + Lint g)) - (sup (L1 γ₁ H₁)).comp (sup ptr) =
      sup (ptr (m := Fin 2) (k := Fin 2) ∘ₗ Lint g) := by
  rw [← sup_comp, ← sup_comp, ← sup_sub, defect_eq]

/-- **Main bound.** For dephasing rates `γ₁, γ₂ ≥ 0`, Hermitian `H₁, H₂` and real coupling `g`,
with `L = L₁ ⊗ id + id ⊗ L₂ − i[g Z⊗X, ·]` and `R = tr₂` (Hilbert–Schmidt operator norm):
`‖R e^{tL} − e^{tL₁} R‖ ≤ t · 2√2 |g|` for all `t ≥ 0`. Contractivity of both semigroups is
*derived* (HS-dissipativity), not assumed. -/
theorem norm_ptr_exp_sub_le {γ₁ γ₂ : ℝ} (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    {H₁ H₂ : Matrix (Fin 2) (Fin 2) ℂ} (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian) (g : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(sup (ptr (m := Fin 2) (k := Fin 2))).comp
        (NormedSpace.exp (t • sup (L0 γ₁ H₁ γ₂ H₂ + Lint g))) -
      (NormedSpace.exp (t • sup (L1 γ₁ H₁))).comp (sup ptr)‖ ≤ t * (2 * Real.sqrt 2 * |g|) := by
  have h := APEX.Unified.Duhamel.norm_sub_le_of_contraction (sup ptr)
    (sup (L0 γ₁ H₁ γ₂ H₂ + Lint g)) (sup (L1 γ₁ H₁)) ht
    (fun s hs => (Ltot_dissipative hγ₁ hγ₂ hH₁ hH₂ g).contractive hs.1)
    (fun s hs => (L1_dissipative hγ₁ hH₁).contractive hs.1)
  rw [sup_defect_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_defect_le g) ht)

/-! ### Counter-model: no coarse generator intertwines -/

/-- The fine-scale matrix unit `|00⟩⟨11|`; its partial trace vanishes. -/
def ρ₀ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => if p = (0, 0) ∧ q = (1, 1) then 1 else 0

theorem ptr_ρ₀ : ptr (k := Fin 2) ρ₀ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ρ₀, Fin.sum_univ_two]

theorem norm_hs_ρ₀ : ‖hs ρ₀‖ = 1 := by
  have h := norm_hs_sq ρ₀
  simp only [ρ₀, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.of_apply] at h
  norm_num at h
  rcases h with h | h
  · exact h
  · have h' := norm_nonneg (hs ρ₀)
    simp only [ρ₀] at h'
    linarith

/-- **Counter-model.** For the interacting generator, *every* bounded real-linear coarse
operator `T` on the coarse HS space has defect at least `2|g|`:
`‖R ∘ L − T ∘ R‖ ≥ 2|g|`, with `R = tr₂` a CPTP map (`ptr_isKrausChannel`). -/
theorem defect_lower_bound (γ₁ : ℝ) (H₁ : Matrix (Fin 2) (Fin 2) ℂ) (γ₂ : ℝ)
    (H₂ : Matrix (Fin 2) (Fin 2) ℂ) (g : ℝ)
    (T : EuclideanSpace ℂ (Fin 2 × Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2 × Fin 2)) :
    2 * |g| ≤ ‖(sup (ptr (m := Fin 2) (k := Fin 2))).comp (sup (L0 γ₁ H₁ γ₂ H₂ + Lint g)) -
      T.comp (sup ptr)‖ := by
  set D := (sup (ptr (m := Fin 2) (k := Fin 2))).comp (sup (L0 γ₁ H₁ γ₂ H₂ + Lint g)) -
      T.comp (sup ptr)
  have hD : D (hs ρ₀) = hs (ptr (Lint g ρ₀)) := by
    have h0 : ptr (L0 γ₁ H₁ γ₂ H₂ ρ₀) = 0 := by
      have := congrArg (fun F => F ρ₀) (ptr_L0 γ₁ H₁ γ₂ H₂)
      simp only [LinearMap.comp_apply] at this
      rw [this, ptr_ρ₀, map_zero]
    simp only [D, FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.comp_apply, sup_apply,
      LinearEquiv.symm_apply_apply, ptr_ρ₀, map_zero, sub_zero, LinearMap.add_apply, map_add, h0,
      zero_add]
  have hentry : ‖hs (ptr (Lint g ρ₀)) ((0 : Fin 2), (1 : Fin 2))‖ = 2 * |g| := by
    rw [hs_apply, ptr_Lint_apply]
    simp [ρ₀, Complex.norm_real]
  calc 2 * |g| = ‖hs (ptr (Lint g ρ₀)) ((0 : Fin 2), (1 : Fin 2))‖ := hentry.symm
    _ ≤ ‖hs (ptr (Lint g ρ₀))‖ := PiLp.norm_apply_le _ _
    _ = ‖D (hs ρ₀)‖ := by rw [hD]
    _ ≤ ‖D‖ * ‖hs ρ₀‖ := D.le_opNorm _
    _ = ‖D‖ := by rw [norm_hs_ρ₀, mul_one]

/-- Hence for `g ≠ 0` there is no coarse generator at all (not even a real-linear, non-GKSL
one) that exactly intertwines, and no exactly consistent coarse semigroup `e^{tA'}`. -/
theorem no_exact_coarse_generator (γ₁ : ℝ) (H₁ : Matrix (Fin 2) (Fin 2) ℂ) (γ₂ : ℝ)
    (H₂ : Matrix (Fin 2) (Fin 2) ℂ) {g : ℝ} (hg : g ≠ 0) :
    ¬ ∃ A' : EuclideanSpace ℂ (Fin 2 × Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2 × Fin 2),
      ∀ t : ℝ, (sup (ptr (m := Fin 2) (k := Fin 2))).comp
        (NormedSpace.exp (t • sup (L0 γ₁ H₁ γ₂ H₂ + Lint g))) =
          (NormedSpace.exp (t • A')).comp (sup ptr) := by
  rintro ⟨A', hA'⟩
  have h := (APEX.Unified.comp_exp_iff _ _ _).1 hA'
  have hb := defect_lower_bound γ₁ H₁ γ₂ H₂ g A'
  rw [h, sub_self, norm_zero] at hb
  have : 0 < |g| := abs_pos.2 hg
  linarith

end TwoQubit

end APEX.Unified.GKSLCoarse

