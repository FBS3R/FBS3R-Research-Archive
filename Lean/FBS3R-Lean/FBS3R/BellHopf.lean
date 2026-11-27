/-
# Bell correlations, CHSH/Tsirelson and the Hopf map

Sources: *A Hopf-Bundle Holonomy Representation of Spin-Singlet Bell Correlations* (PRA
version, 2026-04-30) and *Compact Simply-Connected Cosmology and the Geometric Origin of
Quantum Nonlocality …* (2026-04-15).

Machine-checked here:
* **CHSH bound for every local hidden-variable model** (any probability space, any
  measurable `±1` response functions): `|S| ≤ 2`.
* **Tsirelson-type bound for the singlet kernel** `E(a,b) = -⟪a,b⟫` for unit vectors in
  *any* real inner-product space: `|S| ≤ 2√2`; and the PRA settings give exactly `S = -2√2`.
* Hence (PRA Thm "CHSH obstruction") **no LHV model reproduces the kernel** at those settings.
* **Chern-charge rigidity** (PRA Thm `thm:chernrigidity`): for `q ∈ ℤ`,
  `(∀ θ ∈ [0,π], cos(q(π-θ)) = -cos θ) ↔ q = 1 ∨ q = -1`.
* **Hopf map** `S³ → S²`: `|2 z w̄|² + (|z|²-|w|²)² = (|z|²+|w|²)²`, and invariance under
  the common `U(1)` phase (the Hopf fibre).
* **Error found** in the 2026-04-15 paper (Thm `thm:berry-bell`): for
  `|Φ⁺⟩ = (|00⟩+|11⟩)/√2` one has `⟨σ_y⊗σ_y⟩ = -1` but `⟨σ_x⊗σ_x⟩ = +1`, so
  `E(a,b) = -cos θ_{ab}` is false for `Φ⁺` (it holds for the singlet `Ψ⁻`, checked too).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.BigOperators

namespace FBS3R.Bell

open MeasureTheory Real

/-! ## 1. CHSH inequality for local hidden variables -/

lemma chsh_pointwise {x x' y y' : ℝ} (hx : x = 1 ∨ x = -1) (hx' : x' = 1 ∨ x' = -1)
    (hy : y = 1 ∨ y = -1) (hy' : y' = 1 ∨ y' = -1) :
    |x * y + x * y' + x' * y - x' * y'| ≤ 2 := by
  rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hy' with rfl | rfl <;> norm_num

/-- A local hidden-variable model: hidden variable space `Λ` with probability measure `μ`,
Alice's responses `A a λ ∈ {±1}`, Bob's responses `B b λ ∈ {±1}` (measurable). -/
structure LHV (Λ : Type*) [MeasurableSpace Λ] (SA SB : Type*) where
  μ : Measure Λ
  prob : IsProbabilityMeasure μ
  A : SA → Λ → ℝ
  B : SB → Λ → ℝ
  measA : ∀ a, Measurable (A a)
  measB : ∀ b, Measurable (B b)
  pmA : ∀ a l, A a l = 1 ∨ A a l = -1
  pmB : ∀ b l, B b l = 1 ∨ B b l = -1

variable {Λ : Type*} [MeasurableSpace Λ] {SA SB : Type*}

/-- Correlation of an LHV model. -/
noncomputable def LHV.E (M : LHV Λ SA SB) (a : SA) (b : SB) : ℝ :=
  ∫ l, M.A a l * M.B b l ∂M.μ

lemma LHV.integrable (M : LHV Λ SA SB) (a : SA) (b : SB) :
    Integrable (fun l => M.A a l * M.B b l) M.μ := by
  haveI := M.prob
  refine Integrable.of_bound ((M.measA a).mul (M.measB b)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun l => ?_)
  rcases M.pmA a l with h | h <;> rcases M.pmB b l with h' | h' <;> simp [h, h']

/-- **CHSH**: every LHV model satisfies `|E(a,b)+E(a,b')+E(a',b)-E(a',b')| ≤ 2`. -/
theorem chsh (M : LHV Λ SA SB) (a a' : SA) (b b' : SB) :
    |M.E a b + M.E a b' + M.E a' b - M.E a' b'| ≤ 2 := by
  haveI := M.prob
  have hi := M.integrable
  have : M.E a b + M.E a b' + M.E a' b - M.E a' b'
      = ∫ l, (M.A a l * M.B b l + M.A a l * M.B b' l + M.A a' l * M.B b l
              - M.A a' l * M.B b' l) ∂M.μ := by
    simp only [LHV.E]
    rw [integral_sub, integral_add, integral_add]
    all_goals first
      | exact hi _ _
      | exact (hi _ _).add (hi _ _)
      | exact ((hi _ _).add (hi _ _)).add (hi _ _)
  rw [this]
  have hb := norm_integral_le_of_norm_le_const (μ := M.μ) (C := 2)
    (f := fun l => M.A a l * M.B b l + M.A a l * M.B b' l + M.A a' l * M.B b l
              - M.A a' l * M.B b' l)
    (Filter.Eventually.of_forall fun l =>
      chsh_pointwise (M.pmA a l) (M.pmA a' l) (M.pmB b l) (M.pmB b' l))
  simpa [Real.norm_eq_abs] using hb

/-! ## 2. Singlet kernel: Tsirelson bound and its saturation -/

section Quantum

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Tsirelson bound for the singlet kernel** `E(a,b) = -⟪a,b⟫` with unit vectors. -/
theorem tsirelson_singlet (a a' b b' : V) (ha : ‖a‖ = 1) (ha' : ‖a'‖ = 1)
    (hb : ‖b‖ = 1) (hb' : ‖b'‖ = 1) :
    |(-inner ℝ a b) + (-inner ℝ a b') + (-inner ℝ a' b) - (-inner ℝ a' b')|
      ≤ 2 * √2 := by
  have e : (-inner ℝ a b) + (-inner ℝ a b') + (-inner ℝ a' b) - (-inner ℝ a' b')
      = -(inner ℝ a (b + b') + inner ℝ a' (b - b')) := by
    rw [inner_add_right, inner_sub_right]; ring
  rw [e, abs_neg]
  have h1 : |inner ℝ a (b + b')| ≤ ‖b + b'‖ := by
    have := abs_real_inner_le_norm a (b + b'); rwa [ha, one_mul] at this
  have h2 : |inner ℝ a' (b - b')| ≤ ‖b - b'‖ := by
    have := abs_real_inner_le_norm a' (b - b'); rwa [ha', one_mul] at this
  have par : ‖b + b'‖ ^ 2 + ‖b - b'‖ ^ 2 = 4 := by
    have := norm_add_sq_real b b'
    have := norm_sub_sq_real b b'
    nlinarith [hb, hb']
  have hs : (2 * √2) ^ 2 = 8 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hpos : 0 ≤ 2 * √2 := by positivity
  have hsum : ‖b + b'‖ + ‖b - b'‖ ≤ 2 * √2 := by
    apply abs_le_of_sq_le_sq' _ hpos |>.2
    nlinarith [sq_nonneg (‖b + b'‖ - ‖b - b'‖)]
  calc |inner ℝ a (b + b') + inner ℝ a' (b - b')|
      ≤ |inner ℝ a (b + b')| + |inner ℝ a' (b - b')| := abs_add_le _ _
    _ ≤ ‖b + b'‖ + ‖b - b'‖ := add_le_add h1 h2
    _ ≤ 2 * √2 := hsum

/-- Singlet kernel in the plane, `E(a,b) = -(a₁b₁ + a₂b₂)`. -/
def Eplane (a b : ℝ × ℝ) : ℝ := -(a.1 * b.1 + a.2 * b.2)

/-- PRA settings `a=(1,0), a'=(0,1), b=(1,1)/√2, b'=(1,-1)/√2` give `S = -2√2`. -/
theorem chsh_value_PRA :
    let a : ℝ × ℝ := (1, 0); let a' : ℝ × ℝ := (0, 1)
    let b : ℝ × ℝ := (1 / √2, 1 / √2); let b' : ℝ × ℝ := (1 / √2, -(1 / √2))
    Eplane a b + Eplane a b' + Eplane a' b - Eplane a' b' = -(2 * √2) := by
  intro a a' b b'
  simp only [Eplane, a, a', b, b']
  have h : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : √2 ≠ 0 := by positivity
  field_simp
  linear_combination 2 * h

/-- **No local hidden-variable model reproduces the singlet/holonomy kernel**
(PRA Thm "CHSH obstruction"). -/
theorem no_LHV_reproduces_singlet (M : LHV Λ (ℝ × ℝ) (ℝ × ℝ)) :
    ¬ (∀ a b, M.E a b = Eplane a b) := by
  intro hM
  have h := chsh M (1, 0) (0, 1) (1 / √2, 1 / √2) (1 / √2, -(1 / √2))
  rw [hM, hM, hM, hM, chsh_value_PRA, abs_neg, abs_of_pos (by positivity)] at h
  have : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end Quantum

/-! ## 3. Chern-charge rigidity -/

/-- **Chern-charge rigidity** (PRA Thm `thm:chernrigidity`). -/
theorem chern_rigidity (q : ℤ) :
    (∀ θ ∈ Set.Icc (0 : ℝ) π, Real.cos (q * (π - θ)) = -Real.cos θ) ↔ q = 1 ∨ q = -1 := by
  constructor
  · intro H
    by_contra hq
    push_neg at hq
    rcases eq_or_ne q 0 with rfl | hq0
    · have := H (π / 2) ⟨by positivity, by linarith [pi_pos]⟩
      simp at this
    · -- |q| ≥ 2
      have hq2 : (2 : ℝ) ≤ |(q : ℝ)| := by
        have hqi : 2 ≤ |q| := by
          rcases lt_trichotomy q 0 with h | h | h
          · rw [abs_of_neg h]; omega
          · exact absurd h hq0
          · rw [abs_of_pos h]; omega
        rw [← Int.cast_abs]; exact_mod_cast hqi
      set x : ℝ := 2 * π / |(q : ℝ)|
      have hqa : 0 < |(q : ℝ)| := by linarith
      have hx0 : 0 < x := by positivity
      have hxπ : x ≤ π := by
        rw [div_le_iff₀ hqa]; nlinarith [pi_pos]
      have := H (π - x) ⟨by linarith, by linarith⟩
      have hqx : (q : ℝ) * (π - (π - x)) = (SignType.sign (q : ℝ) : ℝ) * (2 * π) := by
        simp only [sub_sub_cancel, x]
        rcases lt_or_gt_of_ne (show (q : ℝ) ≠ 0 by exact_mod_cast hq0) with h | h
        · rw [abs_of_neg h, sign_neg h]; field_simp; all_goals simp
        · rw [abs_of_pos h, sign_pos h]; field_simp; all_goals simp
      rw [hqx, Real.cos_pi_sub, neg_neg] at this
      have hc1 : Real.cos ((SignType.sign (q : ℝ) : ℝ) * (2 * π)) = 1 := by
        rcases lt_or_gt_of_ne (show (q : ℝ) ≠ 0 by exact_mod_cast hq0) with h | h
        · rw [sign_neg h]; simp
        · rw [sign_pos h]; simp
      rw [hc1] at this
      have := (Real.cos_eq_one_iff_of_lt_of_lt (x := x) (by linarith [pi_pos])
        (by linarith [pi_pos])).mp this.symm
      linarith
  · rintro (rfl | rfl) θ _
    · simp [Real.cos_pi_sub]
    · simp [Real.cos_neg, Real.cos_pi_sub]

/-! ## 4. The Hopf map `S³ → S²` -/

/-- `hopf(z,w) = (2 z w̄, |z|²-|w|²) ∈ ℂ × ℝ ≅ ℝ³`. -/
noncomputable def hopf (z w : ℂ) : ℂ × ℝ := (2 * z * (starRingEnd ℂ) w, Complex.normSq z - Complex.normSq w)

/-- The Hopf map sends the 3-sphere `|z|²+|w|² = 1` into the 2-sphere. -/
theorem hopf_sphere (z w : ℂ) :
    Complex.normSq (hopf z w).1 + (hopf z w).2 ^ 2 = (Complex.normSq z + Complex.normSq w) ^ 2 := by
  simp only [hopf, Complex.normSq_mul, Complex.normSq_conj]
  have : Complex.normSq (2 : ℂ) = 4 := by simp [Complex.normSq]; norm_num
  rw [this]; ring

theorem hopf_S3_to_S2 (z w : ℂ) (h : Complex.normSq z + Complex.normSq w = 1) :
    Complex.normSq (hopf z w).1 + (hopf z w).2 ^ 2 = 1 := by
  rw [hopf_sphere, h, one_pow]

/-- The Hopf map is constant on `U(1)` fibres `(z,w) ↦ (λz, λw)`, `|λ| = 1`. -/
theorem hopf_fibre (z w l : ℂ) (hl : Complex.normSq l = 1) : hopf (l * z) (l * w) = hopf z w := by
  have hl' : l * (starRingEnd ℂ) l = 1 := by
    rw [Complex.mul_conj, hl]; simp
  simp only [hopf, map_mul, Complex.normSq_mul, hl, one_mul, Prod.mk.injEq, and_true]
  linear_combination (2 * z * (starRingEnd ℂ) w) * hl'

/-! ## 5. Bell state vs singlet: an error in the 2026-04-15 paper -/

section Pauli

open Matrix
open scoped Kronecker

def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Unnormalised `|00⟩ + |11⟩` (norm² = 2) and `|01⟩ - |10⟩` (norm² = 2). -/
def Φp : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0
def Ψm : Fin 2 × Fin 2 → ℂ := fun p =>
  if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- `⟨ψ| A ⊗ B |ψ⟩` (unnormalised). -/
def expval (ψ : Fin 2 × Fin 2 → ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  star ψ ⬝ᵥ ((A ⊗ₖ B) *ᵥ ψ)

lemma expval_eq (ψ : Fin 2 × Fin 2 → ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    expval ψ A B = ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
      star (ψ (i, j)) * (A i k * B j l * ψ (k, l)) := by
  simp only [expval, dotProduct, mulVec, Fintype.sum_prod_type, kroneckerMap_apply,
    Pi.star_apply, Finset.mul_sum]

/-- For `Φ⁺`: `⟨σx⊗σx⟩ = +1`, `⟨σy⊗σy⟩ = -1`, `⟨σz⊗σz⟩ = +1` (after dividing by norm² 2).
Hence `E(a,a) = +1 ≠ -cos 0` for `a = x̂`: the claimed `E = -cos θ` fails for `Φ⁺`. -/
theorem bell_Phi_plus :
    expval Φp σx σx = 2 ∧ expval Φp σy σy = -2 ∧ expval Φp σz σz = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [expval_eq]; simp [Fin.sum_univ_two, Φp, σx, σy, σz]; try ring_nf
    try simp [Complex.ext_iff]; try norm_num

/-- For the singlet `Ψ⁻`: `⟨σᵢ⊗σᵢ⟩ = -1` for `i = x, y, z`, consistent with `E = -a·b`. -/
theorem singlet_Psi_minus :
    expval Ψm σx σx = -2 ∧ expval Ψm σy σy = -2 ∧ expval Ψm σz σz = -2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [expval_eq]; simp [Fin.sum_univ_two, Ψm, σx, σy, σz]; try ring_nf
    try simp [Complex.ext_iff]; try norm_num

end Pauli

end FBS3R.Bell
