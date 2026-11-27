/-
# Killing–Beltrami algebra on the round three-sphere: the algebraic core

Source: *Killing–Beltrami algebra and exact reductions of Navier–Stokes flow on the
three-sphere* (2026-09-21/23) and its companion *Geometric Reduction, Killing Response…*.

What is formalised (no `sorry`, no extra axioms):

1. **Representation-defect theorem** (Thm `thm:representationdefect`), in full abstract
   generality: for any two *commuting* representations `P` of `L₁` and `Q` of `L₂` on a
   module `M` (the two `su(2)` factors of `so(4)` acting by Lie derivative on a curl shell
   `E_{k,σ}`) and any scalars `a, b`, the operator `D(x,y) = a·P x + b·Q y` satisfies
   `[D m, D n] = a²·P[x,x'] + b²·Q[y,y']`, hence
   `Ω(m,n) = [D m, D n] - D[m,n] = (a²-a)·P[x,x'] + (b²-b)·Q[y,y']`.
   With the paper's coefficients `a = k/(k+2)`, `b = (k+4)/(k+2)` this yields exactly
   `-2k/(k+2)²` and `2(k+4)/(k+2)²`.
2. **Coefficient identities**: the Killing–Beltrami polarization coefficient
   `(μ_{k,σ}-μ_{0,τ})/(2μ_{k,σ}) = (k+2-2τσ)/(2(k+2))`, its two chiral values,
   the decomposition `D = ad + 2/(k+2)(ad_{m_{-σ}} - ad_{m_σ})` (eq. `Dminusad`).
3. **Spectral bookkeeping of signed curl shells**: spins `j_τ = (k+1+τσ)/2`,
   `dim E_{k,σ} = (2j₊+1)(2j₋+1) = (k+1)(k+3)`, the Casimir identity
   `Δ_iso = 2 curl²`, the Stokes eigenvalue `κ_k = curl² - 4/R² = k(k+4)/R²`,
   the closed structure-coefficient values (Cor. "Two explicit chiral values"),
   and the `s = 2` weight `(k+1)(k+3)/(k+2)² = 1 - 1/(k+2)²` (eq. `weightedM`).

What is **not** formalised: the differential-geometric input (that the shells
`E_{k,σ}` are the curl eigenspaces with eigenvalue `σ(k+2)/R`, that Killing fields act on
them through the stated `SU(2)×SU(2)` spins, that `Q` is the Leray-projected nonlinearity).
Mathlib currently has no Hodge theory / curl operator on Riemannian 3-manifolds, so these
enter as the (standard) hypotheses of the algebraic statements below.
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace FBS3R.KillingBeltrami

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## 1. Representation defect of the Killing precession operator -/

section Defect

variable {K : Type*} [CommRing K]
variable {L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra K L₁] [LieRing L₂] [LieAlgebra K L₂]
variable {M : Type*} [AddCommGroup M] [Module K M]

/-- The precession operator `D(m) = a·P(m₊) + b·Q(m₋)` on a shell. -/
def D (P : L₁ →ₗ⁅K⁆ Module.End K M) (Q : L₂ →ₗ⁅K⁆ Module.End K M) (a b : K)
    (m : L₁ × L₂) : Module.End K M :=
  a • P m.1 + b • Q m.2

variable (P : L₁ →ₗ⁅K⁆ Module.End K M) (Q : L₂ →ₗ⁅K⁆ Module.End K M) (a b : K)

/-- Commutator of two precession operators (eq. `DcommD`). The only hypothesis is that the
two simple factors act by commuting operators, as `su(2)₊` and `su(2)₋` do inside `so(4)`. -/
theorem D_comm (hPQ : ∀ x y, ⁅P x, Q y⁆ = 0) (m n : L₁ × L₂) :
    ⁅D P Q a b m, D P Q a b n⁆ = (a * a) • P ⁅m.1, n.1⁆ + (b * b) • Q ⁅m.2, n.2⁆ := by
  have hQP : ∀ x y, ⁅Q y, P x⁆ = 0 := fun x y => by
    rw [← lie_skew, hPQ, neg_zero]
  simp only [D, add_lie, lie_add, smul_lie, lie_smul, hPQ, hQP, LieHom.map_lie, smul_zero,
    add_zero, zero_add, smul_smul]

/-- **Representation defect** (eq. `Omega`): `Ω(m,n) = [D m, D n] - D [m,n]`. -/
theorem defect (hPQ : ∀ x y, ⁅P x, Q y⁆ = 0) (m n : L₁ × L₂) :
    ⁅D P Q a b m, D P Q a b n⁆ - D P Q a b (⁅m.1, n.1⁆, ⁅m.2, n.2⁆)
      = (a * a - a) • P ⁅m.1, n.1⁆ + (b * b - b) • Q ⁅m.2, n.2⁆ := by
  rw [D_comm P Q a b hPQ]
  simp only [D, sub_smul]
  abel

end Defect

section Coefficients

/-- Same-chirality coefficient `a_k = k/(k+2)` and opposite-chirality `b_k = (k+4)/(k+2)`. -/
noncomputable def aK (k : ℕ) : ℝ := k / (k + 2)
noncomputable def bK (k : ℕ) : ℝ := (k + 4) / (k + 2)

lemma kp2_ne (k : ℕ) : (k : ℝ) + 2 ≠ 0 := by positivity

/-- Paper's closed defect coefficients: `a²-a = -2k/(k+2)²`, `b²-b = 2(k+4)/(k+2)²`. -/
theorem defect_coeffs (k : ℕ) :
    aK k * aK k - aK k = -(2 * k) / ((k : ℝ) + 2) ^ 2 ∧
    bK k * bK k - bK k = 2 * ((k : ℝ) + 4) / ((k : ℝ) + 2) ^ 2 := by
  have := kp2_ne k
  constructor <;> (simp only [aK, bK]; field_simp; ring)

/-- For `k ≥ 1` both defect coefficients are nonzero, so `m ↦ D_{k,σ}(m)` is *not* a Lie
algebra representation unless both brackets act trivially (Thm `thm:representationdefect`). -/
theorem defect_coeffs_ne_zero {k : ℕ} (hk : 1 ≤ k) :
    aK k * aK k - aK k ≠ 0 ∧ bK k * bK k - bK k ≠ 0 := by
  obtain ⟨h1, h2⟩ := defect_coeffs k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [h1, h2]
  constructor
  · apply div_ne_zero (by linarith) (by positivity)
  · apply div_ne_zero (by positivity) (by positivity)

/-- eq. `Dminusad`: `a·x + b·y = (x + y) + 2/(k+2)·(y - x)` in any real vector space,
i.e. `D_{k,σ}(m) = ad_m + 2/(k+2)(ad_{m_{-σ}} - ad_{m_σ})`. -/
theorem D_minus_ad {V : Type*} [AddCommGroup V] [Module ℝ V] (k : ℕ) (x y : V) :
    aK k • x + bK k • y = (x + y) + (2 / ((k : ℝ) + 2)) • (y - x) := by
  have := kp2_ne k
  have ha : aK k = 1 - 2 / ((k : ℝ) + 2) := by unfold aK; field_simp; ring
  have hb : bK k = 1 + 2 / ((k : ℝ) + 2) := by unfold bK; field_simp; ring
  rw [ha, hb, sub_smul, add_smul, one_smul, one_smul, smul_sub]
  abel

/-- Curl eigenvalue on the signed shell `E_{k,σ}` of `S³(R)`: `μ_{k,σ} = σ(k+2)/R`. -/
noncomputable def μ (R : ℝ) (k : ℕ) (σ : ℤ) : ℝ := σ * (k + 2) / R

/-- **Exact Killing–Beltrami polarization coefficient** (Thm `thm:KBidentity`):
`(μ_{k,σ} - μ_{0,τ}) / (2 μ_{k,σ}) = (k + 2 - 2τσ) / (2(k+2))` for `σ, τ = ±1`. -/
theorem KB_coefficient (R : ℝ) (hR : R ≠ 0) (k : ℕ) (σ τ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    (μ R k σ - μ R 0 τ) / (2 * μ R k σ) = ((k : ℝ) + 2 - 2 * τ * σ) / (2 * ((k : ℝ) + 2)) := by
  have hk := kp2_ne k
  have hσ2 : (σ : ℝ) * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ0 : (σ : ℝ) ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  unfold μ
  field_simp
  push_cast
  linear_combination (2 * (τ:ℝ)) * hσ2

/-- The two chiral values (eqs. `samechir`, `oppchir`): `2Q(K_σ,v) = k/(k+2)[K_σ,v]` and
`2Q(K_{-σ},v) = (k+4)/(k+2)[K_{-σ},v]`. -/
theorem chiral_values (k : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    ((k : ℝ) + 2 - 2 * σ * σ) / ((k : ℝ) + 2) = aK k ∧
    ((k : ℝ) + 2 - 2 * (-σ) * σ) / ((k : ℝ) + 2) = bK k := by
  have hσ2 : (σ : ℝ) * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  unfold aK bK
  constructor
  · congr 1; linear_combination (-2:ℝ) * hσ2
  · congr 1; push_cast; linear_combination (2:ℝ) * hσ2

end Coefficients

/-! ## 3. Spectral bookkeeping of signed curl shells on `S³(R)` -/

section Spectral

/-- `SU(2)_τ` spin on `E_{k,σ}`: `j_τ = (k + 1 + τσ)/2`. -/
noncomputable def spin (k : ℕ) (τσ : ℤ) : ℝ := ((k : ℝ) + 1 + τσ) / 2

/-- `dim E_{k,σ} = (2j₊+1)(2j₋+1) = (k+1)(k+3)` (for either sign `σ`). -/
theorem shell_dim (k : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (2 * spin k σ + 1) * (2 * spin k (-σ) + 1) = ((k : ℝ) + 1) * ((k : ℝ) + 3) := by
  unfold spin; rcases hσ with rfl | rfl <;> push_cast <;> ring

/-- **Casimir identity** `Δ_iso = 2 curl²` on `E_{k,σ}` (Thm `thm:stokesiso`): with the
normalisation `[X_a,X_b] = (2/R) ε_{abc} X_c`, `-Σ_a (X_a^τ)²` acts by `(4/R²) j_τ(j_τ+1)`,
and the sum over both factors equals `2 μ_{k,σ}²`. -/
theorem casimir_eq_two_curl_sq (R : ℝ) (hR : R ≠ 0) (k : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    4 / R ^ 2 * (spin k σ * (spin k σ + 1) + spin k (-σ) * (spin k (-σ) + 1))
      = 2 * (μ R k σ) ^ 2 := by
  unfold spin μ; rcases hσ with rfl | rfl <;> (push_cast; field_simp; ring)

/-- Stokes (Ebin–Marsden) eigenvalue: `A = ½Δ_iso - 4/R² = curl² - 4/R² = k(k+4)/R²`. -/
theorem stokes_eigenvalue (R : ℝ) (hR : R ≠ 0) (k : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (μ R k σ) ^ 2 - 4 / R ^ 2 = (k : ℝ) * (k + 4) / R ^ 2 := by
  unfold μ; rcases hσ with rfl | rfl <;> (push_cast; field_simp; ring)

/-- The Killing shells (`k = 0`) are exactly the Stokes kernel, and the first toric
non-constant level (`k = 2`) gives the decay rate `12ν/R²` of eq. `T2decay`. -/
theorem stokes_k0_k2 : ((0 : ℕ) : ℝ) * (0 + 4) = 0 ∧ ((2 : ℕ) : ℝ) * (2 + 4) = 12 := by
  norm_num

/-- Closed structure coefficients (Cor. "Two explicit chiral values"):
`(k+2-2τσ)²/(k+2)² · j_τ(j_τ+1)` equals `k²(k+4)/(4(k+2))` for `τ = σ` and
`k(k+4)²/(4(k+2))` for `τ = -σ`. -/
theorem structure_coefficients (k : ℕ) :
    ((k : ℝ) + 2 - 2) ^ 2 / ((k : ℝ) + 2) ^ 2 * (spin k 1 * (spin k 1 + 1))
        = (k : ℝ) ^ 2 * (k + 4) / (4 * (k + 2)) ∧
    ((k : ℝ) + 2 + 2) ^ 2 / ((k : ℝ) + 2) ^ 2 * (spin k (-1) * (spin k (-1) + 1))
        = (k : ℝ) * (k + 4) ^ 2 / (4 * (k + 2)) := by
  have := kp2_ne k
  unfold spin
  constructor <;> (push_cast; field_simp; ring)

/-- `s = 2` weight in the derivative-budget barrier (eq. `weightedM`):
`(k+1)(k+3)/(k+2)² = 1 - 1/(k+2)²`. -/
theorem weight_s2 (k : ℕ) :
    ((k : ℝ) + 1) * (k + 3) / ((k : ℝ) + 2) ^ 2 = 1 - 1 / ((k : ℝ) + 2) ^ 2 := by
  have := kp2_ne k
  field_simp; ring

/-- The paper's Yang–Mills companion (2026-04-19) asserts a lowest transverse eigenvalue
`3/R²`.  With the curl spectrum `μ² = (k+2)²/R²` used throughout the Killing–Beltrami papers,
`curl²` never takes the value `3/R²` (its minimum is `4/R²`), and neither does the Stokes
operator `k(k+4)/R²` (values `0, 5, 12, …`).  This records the internal inconsistency. -/
theorem no_three_in_curl_or_stokes_spectrum (k : ℕ) :
    ((k : ℝ) + 2) ^ 2 ≠ 3 ∧ (k : ℝ) * (k + 4) ≠ 3 ∧ 4 ≤ ((k : ℝ) + 2) ^ 2 := by
  have hk : (0 : ℝ) ≤ k := by positivity
  refine ⟨?_, ?_, by nlinarith⟩
  · nlinarith
  · intro h
    have h' : (k : ℤ) * (k + 4) = 3 := by exact_mod_cast h
    rcases k with _ | _ | k <;> push_cast at h' <;> nlinarith

end Spectral

end FBS3R.KillingBeltrami
