import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Block-Hamiltonian lower bounds (the "block" route to a spectral gap)

**Scope.** Elementary, fully general linear algebra / quadratic-form estimates for
block operators `H = [[A, B†], [B, C]]` and for tridiagonal hierarchies of scales.
**Nothing here is specific to, or proves anything about, Yang–Mills.** In particular the
uniformity of the constants `α, γ, b` (in the lattice spacing `a` and the volume `L`)
is always a *hypothesis*; it is never derived. See §5 for the precise caveats.

Notation: `μ(α,γ,b) = ½ (α + γ − √((α−γ)² + 4b²))` (`mu`), `ν = ½ (α + γ + √(…))` (`nu`).

## 1. Scalar core (all real `x, y`, any real `b`)
* `scalar_bound`: `μ (x² + y²) ≤ α x² − 2 b x y + γ y²`.
* `scalar_bound_sharp`: equality for some `(x, y) ≠ 0`.
* `mu_isEigenvalue`, `eigenvalue_eq_mu_or_nu`, `mu_le_eigenvalue`: `μ` is an eigenvalue of
  `[[α, b], [b, γ]]` (explicit eigenvector), every real eigenvalue is `μ` or `ν`, and so
  `μ` is the smallest one.
* `mu_pos_iff`: `0 < μ ↔ 0 < α + γ ∧ b² < α γ`; `mu_pos` : `α, γ > 0, b² < αγ ⇒ μ > 0`.

## 2. Operator version (`𝕜 = ℝ` or `ℂ`, arbitrary inner product spaces `E₁, E₂`)
* `blockForm A B C u v = Re⟪Au,u⟫ + 2 Re⟪Bu,v⟫ + Re⟪Cv,v⟫` (`A, C` linear, `B` bounded).
* `block_lower_bound`: `Re⟪Au,u⟫ ≥ α‖u‖²`, `Re⟪Cv,v⟫ ≥ γ‖v‖²`, `‖B‖ ≤ b` ⇒
  `blockForm ≥ μ (‖u‖² + ‖v‖²)`.
* `blockOp A B C` (complete `E₁, E₂`) is the operator `ψ ↦ (Aψ₁ + B†ψ₂, Bψ₁ + Cψ₂)` on the
  Hilbert sum `WithLp 2 (E₁ × E₂)`; `re_inner_blockOp`: `Re⟪Hψ,ψ⟫ = blockForm ψ₁ ψ₂`;
  `blockOp_lower_bound`: `Re⟪Hψ,ψ⟫ ≥ μ ‖ψ‖²`.

## 3. Schur-complement criteria
* `schur_iff` (scalar): `(∀ x y, m(x²+y²) ≤ αx² − 2bxy + γy²) ↔
  m ≤ α ∧ m ≤ γ ∧ b² ≤ (α−m)(γ−m)` (PSD of `[[α−m, −b],[−b, γ−m]]`).
* `le_mu_iff`: the Schur condition is equivalent to `m ≤ μ`; `scalar_best_constant`:
  `μ` is the best constant.
* `block_lower_bound_of_schur` (operator version, sufficiency).

## 4. Hierarchies of scales (tridiagonal chains)
* `chainForm A B n u = Σ_{i≤n} Re⟪A_i u_i, u_i⟫ + 2 Σ_{i<n} Re⟪B_i u_i, u_{i+1}⟫`,
  `B_i : E_i →L E_{i+1}`.
* `chain_lower_bound` (weighted Gershgorin): weights `t_i > 0`, `‖B_i‖ ≤ b_i`,
  `m ≤ α_i − b_{i−1}/t_{i−1} − b_i t_i` (missing terms at the ends are `0`, see `leftW`,
  `rightW`) ⇒ `chainForm ≥ m Σ_{i≤n} ‖u_i‖²`. Unweighted: `chain_lower_bound_gershgorin`
  (`m ≤ α_i − b_{i−1} − b_i`). Uniform: `chain_lower_bound_uniform` (`α − 2b`).
* Infinite hierarchy (index `ℕ`), **domain = finitely supported families** (`u_i = 0` for
  `i > N`): `chainForm_stable` (the form does not depend on the truncation `M ≥ N`, so it is
  well defined on this domain), `hierarchy_lower_bound` (weighted, hypothesis for all `i`),
  `hierarchy_lower_bound_uniform` (`sup ‖B_i‖ ≤ b`, `inf α_i ≥ α` ⇒ bound `α − 2b`).
  No closure / self-adjoint extension to `ℓ²`-sums is constructed.

## 5. Transfer-matrix application (abstract)
* `transfer_of_generator_bound`: on a set `S`, `Re⟪(I−T)ψ,ψ⟫ / a ≥ Δ‖ψ‖²` ⇒
  `Re⟪Tψ,ψ⟫ ≤ (1 − aΔ)‖ψ‖² ≤ e^{−aΔ}‖ψ‖²`.
* `transfer_of_block_generator`: if `Re⟪(I−T)ψ,ψ⟫ = a · blockForm A B C ψ₁ ψ₂` on `S`, with
  the hypotheses of §2 and `Δ ≤ μ(α,γ,b)`, then `Re⟪Tψ,ψ⟫ ≤ e^{−aΔ}‖ψ‖²`;
  `eigenvalue_le_of_block_generator`: real eigenvalues of `T` with eigenvectors in `S` are
  `≤ e^{−aΔ}` (which is the hypothesis `hspec` of `APEX.YM.transfer_bound` on `Ω^⊥`).

**What is NOT proved (caveats).** (i) That any Yang–Mills transfer matrix/generator has such a
block decomposition, or that `α, γ, b` can be chosen **uniformly in `a` and `L`** with
`μ ≥ Δ > 0`: this uniformity is an assumption of §5, not a theorem. (ii) A gap for an
auxiliary (e.g. stochastic / Langevin / heat-bath) generator is **not** the gap of the
quantum Hamiltonian `−(1/a) log T` of the Osterwalder–Schrader reconstruction unless the
generator *is* `(I − T)/a` for the OS transfer matrix `T`. (iii) No unbounded-operator
theory: forms are only evaluated on vectors in the stated domains.
-/

open scoped InnerProductSpace
open RCLike

namespace APEX.YM.BlockGap

set_option linter.unusedSectionVars false

/-! ## 1. Scalar core -/

/-- Smallest eigenvalue of `[[α, b], [b, γ]]`. -/
noncomputable def mu (α γ b : ℝ) : ℝ := (α + γ - √((α - γ) ^ 2 + 4 * b ^ 2)) / 2

/-- Largest eigenvalue of `[[α, b], [b, γ]]`. -/
noncomputable def nu (α γ b : ℝ) : ℝ := (α + γ + √((α - γ) ^ 2 + 4 * b ^ 2)) / 2

section Scalar

variable (α γ b : ℝ)

lemma disc_nonneg : 0 ≤ (α - γ) ^ 2 + 4 * b ^ 2 := by positivity

lemma sq_sqrt_disc : √((α - γ) ^ 2 + 4 * b ^ 2) ^ 2 = (α - γ) ^ 2 + 4 * b ^ 2 :=
  Real.sq_sqrt (disc_nonneg α γ b)

lemma abs_sub_le_sqrt_disc : |α - γ| ≤ √((α - γ) ^ 2 + 4 * b ^ 2) :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg b])

lemma mu_le_left : mu α γ b ≤ α := by
  have := abs_sub_le_sqrt_disc α γ b
  have := neg_abs_le (α - γ)
  unfold mu; linarith

lemma mu_le_right : mu α γ b ≤ γ := by
  have := abs_sub_le_sqrt_disc α γ b
  have := le_abs_self (α - γ)
  unfold mu; linarith

lemma mu_le_nu : mu α γ b ≤ nu α γ b := by
  have := Real.sqrt_nonneg ((α - γ) ^ 2 + 4 * b ^ 2)
  unfold mu nu; linarith

/-- `(α − μ)(γ − μ) = b²`. -/
lemma mu_det : (α - mu α γ b) * (γ - mu α γ b) = b ^ 2 := by
  have h := sq_sqrt_disc α γ b
  unfold mu
  linear_combination h / 4

/-- Characteristic polynomial: `(α − λ)(γ − λ) − b² = (λ − μ)(λ − ν)`. -/
lemma charpoly_eq (l : ℝ) :
    (α - l) * (γ - l) - b ^ 2 = (l - mu α γ b) * (l - nu α γ b) := by
  have h := sq_sqrt_disc α γ b
  unfold mu nu
  linear_combination h / 4

/-- A `2×2` symmetric matrix `[[p, −b],[−b, r]]` with `p, r ≥ 0`, `b² ≤ pr` is PSD. -/
lemma psd2 {p r b : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (h : b ^ 2 ≤ p * r) (x y : ℝ) :
    0 ≤ p * x ^ 2 - 2 * b * x * y + r * y ^ 2 := by
  rcases hp.lt_or_eq with hp | hp
  · have e : p * (p * x ^ 2 - 2 * b * x * y + r * y ^ 2) =
        (p * x - b * y) ^ 2 + (p * r - b ^ 2) * y ^ 2 := by ring
    have : 0 ≤ p * (p * x ^ 2 - 2 * b * x * y + r * y ^ 2) := by
      rw [e]; have := sq_nonneg (p * x - b * y); have := sq_nonneg y
      nlinarith
    by_contra hc
    push Not at hc
    nlinarith
  · subst hp
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    subst hb
    nlinarith [sq_nonneg y]

/-- **Scalar core.** For all real `x, y` and any real `α, γ, b`:
`μ (x² + y²) ≤ α x² − 2 b x y + γ y²`. -/
theorem scalar_bound (x y : ℝ) :
    mu α γ b * (x ^ 2 + y ^ 2) ≤ α * x ^ 2 - 2 * b * x * y + γ * y ^ 2 := by
  have := psd2 (sub_nonneg.mpr (mu_le_left α γ b)) (sub_nonneg.mpr (mu_le_right α γ b))
    (mu_det α γ b).ge x y
  nlinarith

/-- **Sharpness.** The bound `scalar_bound` is attained at some `(x, y) ≠ 0`. -/
theorem scalar_bound_sharp :
    ∃ x y : ℝ, (x, y) ≠ (0, 0) ∧
      α * x ^ 2 - 2 * b * x * y + γ * y ^ 2 = mu α γ b * (x ^ 2 + y ^ 2) := by
  have hd := mu_det α γ b
  by_cases h : b = 0 ∧ α - mu α γ b = 0
  · refine ⟨1, 0, by simp, ?_⟩
    rw [show mu α γ b = α by linarith [h.2], h.1]; ring
  · refine ⟨b, α - mu α γ b, ?_, ?_⟩
    · intro h'
      simp only [Prod.mk.injEq] at h'
      exact h h'
    · linear_combination (α - mu α γ b) * hd

/-- `μ` is an eigenvalue of `[[α, b], [b, γ]]`, with an explicit nonzero eigenvector. -/
theorem mu_isEigenvalue :
    ∃ x y : ℝ, (x, y) ≠ (0, 0) ∧
      α * x + b * y = mu α γ b * x ∧ b * x + γ * y = mu α γ b * y := by
  have hd := mu_det α γ b
  by_cases h : b = 0 ∧ α - mu α γ b = 0
  · refine ⟨1, 0, by simp, ?_, ?_⟩
    · rw [mul_zero, mul_one, mul_one, add_zero]; linarith [h.2]
    · rw [h.1]; ring
  · refine ⟨b, mu α γ b - α, ?_, ?_, ?_⟩
    · intro h'
      simp only [Prod.mk.injEq] at h'
      exact h ⟨h'.1, by linarith [h'.2]⟩
    · ring
    · linear_combination -hd

/-- Every real eigenvalue of `[[α, b], [b, γ]]` is `μ` or `ν`. -/
theorem eigenvalue_eq_mu_or_nu {l x y : ℝ} (hne : (x, y) ≠ (0, 0))
    (h1 : α * x + b * y = l * x) (h2 : b * x + γ * y = l * y) :
    l = mu α γ b ∨ l = nu α γ b := by
  have hx : ((α - l) * (γ - l) - b ^ 2) * x = 0 := by
    linear_combination (γ - l) * h1 - b * h2
  have hy : ((α - l) * (γ - l) - b ^ 2) * y = 0 := by
    linear_combination (α - l) * h2 - b * h1
  have hdet : (α - l) * (γ - l) - b ^ 2 = 0 := by
    by_contra hc
    apply hne
    rw [mul_eq_zero] at hx hy
    simp [hx.resolve_left hc, hy.resolve_left hc]
  rw [charpoly_eq] at hdet
  rcases mul_eq_zero.mp hdet with h | h
  · left; linarith
  · right; linarith

/-- `μ` is the smallest real eigenvalue of `[[α, b], [b, γ]]`. -/
theorem mu_le_eigenvalue {l x y : ℝ} (hne : (x, y) ≠ (0, 0))
    (h1 : α * x + b * y = l * x) (h2 : b * x + γ * y = l * y) : mu α γ b ≤ l := by
  rcases eigenvalue_eq_mu_or_nu α γ b hne h1 h2 with h | h
  · exact h.ge
  · rw [h]; exact mu_le_nu α γ b

/-- **Positivity criterion.** `0 < μ ↔ 0 < α + γ ∧ b² < α γ`. -/
theorem mu_pos_iff : 0 < mu α γ b ↔ 0 < α + γ ∧ b ^ 2 < α * γ := by
  have hs0 := Real.sqrt_nonneg ((α - γ) ^ 2 + 4 * b ^ 2)
  have key : 0 < mu α γ b ↔ √((α - γ) ^ 2 + 4 * b ^ 2) < α + γ := by
    unfold mu; constructor <;> intro h <;> linarith
  rw [key]
  constructor
  · intro h
    have hpos : 0 < α + γ := by linarith
    refine ⟨hpos, ?_⟩
    have := (Real.sqrt_lt' hpos).mp h
    nlinarith
  · rintro ⟨hpos, h⟩
    exact (Real.sqrt_lt' hpos).mpr (by nlinarith)

theorem mu_pos {α γ b : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hb : b ^ 2 < α * γ) :
    0 < mu α γ b :=
  (mu_pos_iff α γ b).mpr ⟨by linarith, hb⟩

/-! ## 3 (scalar). Schur-complement criterion -/

/-- **Schur criterion.** `α x² − 2bxy + γ y² ≥ m(x² + y²)` for all real `x, y` iff
`m ≤ α`, `m ≤ γ` and `b² ≤ (α − m)(γ − m)`. -/
theorem schur_iff (m : ℝ) :
    (∀ x y : ℝ, m * (x ^ 2 + y ^ 2) ≤ α * x ^ 2 - 2 * b * x * y + γ * y ^ 2) ↔
      (m ≤ α ∧ m ≤ γ ∧ b ^ 2 ≤ (α - m) * (γ - m)) := by
  constructor
  · intro h
    have hα : m ≤ α := by have := h 1 0; nlinarith
    have hγ : m ≤ γ := by have := h 0 1; nlinarith
    refine ⟨hα, hγ, ?_⟩
    rcases (sub_nonneg.mpr hα).lt_or_eq with hp | hp
    · have := h b (α - m)
      have e : α * b ^ 2 - 2 * b * b * (α - m) + γ * (α - m) ^ 2 - m * (b ^ 2 + (α - m) ^ 2) =
          (α - m) * ((α - m) * (γ - m) - b ^ 2) := by ring
      by_contra hc; push Not at hc
      nlinarith
    rcases (sub_nonneg.mpr hγ).lt_or_eq with hr | hr
    · have := h (γ - m) b
      have e : α * (γ - m) ^ 2 - 2 * b * (γ - m) * b + γ * b ^ 2 - m * ((γ - m) ^ 2 + b ^ 2) =
          (γ - m) * ((α - m) * (γ - m) - b ^ 2) := by ring
      by_contra hc; push Not at hc
      nlinarith
    · have := h b 1
      rw [← hp, ← hr]
      have e1 : α = m := by linarith
      have e2 : γ = m := by linarith
      subst e1 e2
      nlinarith [sq_nonneg b]
  · rintro ⟨hα, hγ, hb⟩ x y
    have := psd2 (sub_nonneg.mpr hα) (sub_nonneg.mpr hγ) hb x y
    nlinarith

/-- The Schur condition is equivalent to `m ≤ μ`. -/
theorem le_mu_iff (m : ℝ) :
    m ≤ mu α γ b ↔ (m ≤ α ∧ m ≤ γ ∧ b ^ 2 ≤ (α - m) * (γ - m)) := by
  constructor
  · intro hm
    refine (schur_iff α γ b m).mp fun x y => ?_
    have := scalar_bound α γ b x y
    have : m * (x ^ 2 + y ^ 2) ≤ mu α γ b * (x ^ 2 + y ^ 2) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    linarith
  · rintro ⟨hα, hγ, hb⟩
    have hs : √((α - γ) ^ 2 + 4 * b ^ 2) ≤ (α - m) + (γ - m) := by
      refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
      have e : ((α - m) + (γ - m)) ^ 2 - ((α - γ) ^ 2 + 4 * b ^ 2) =
          4 * ((α - m) * (γ - m) - b ^ 2) := by ring
      linarith
    unfold mu; linarith

/-- `μ` is the best constant in `scalar_bound`. -/
theorem scalar_best_constant (m : ℝ) :
    (∀ x y : ℝ, m * (x ^ 2 + y ^ 2) ≤ α * x ^ 2 - 2 * b * x * y + γ * y ^ 2) ↔ m ≤ mu α γ b :=
  (schur_iff α γ b m).trans (le_mu_iff α γ b m).symm

end Scalar

/-! ## 2. Operator version -/

section Operator

variable {𝕜 : Type*} [RCLike 𝕜] {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]

/-- The quadratic form of the block operator `[[A, B†], [B, C]]`:
`Re⟪Au,u⟫ + 2 Re⟪Bu,v⟫ + Re⟪Cv,v⟫`. -/
noncomputable def blockForm (A : E₁ →ₗ[𝕜] E₁) (B : E₁ →L[𝕜] E₂) (C : E₂ →ₗ[𝕜] E₂)
    (u : E₁) (v : E₂) : ℝ :=
  re ⟪A u, u⟫_𝕜 + 2 * re ⟪B u, v⟫_𝕜 + re ⟪C v, v⟫_𝕜

/-- `|Re⟪Bu, v⟫| ≤ b ‖u‖ ‖v‖` when `‖B‖ ≤ b`. -/
lemma neg_le_re_inner_apply (B : E₁ →L[𝕜] E₂) {b : ℝ} (hB : ‖B‖ ≤ b) (u : E₁) (v : E₂) :
    -(b * ‖u‖ * ‖v‖) ≤ re ⟪B u, v⟫_𝕜 := by
  have h1 := abs_re_le_norm (⟪B u, v⟫_𝕜)
  have h2 := norm_inner_le_norm (𝕜 := 𝕜) (B u) v
  have h3 : ‖B u‖ ≤ b * ‖u‖ := (B.le_opNorm u).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have h4 : ‖B u‖ * ‖v‖ ≤ b * ‖u‖ * ‖v‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  have := neg_abs_le (re ⟪B u, v⟫_𝕜)
  linarith

/-- **Operator block bound.** If `Re⟪Au,u⟫ ≥ α‖u‖²`, `Re⟪Cv,v⟫ ≥ γ‖v‖²` and `‖B‖ ≤ b`, then
`blockForm A B C u v ≥ μ(α,γ,b) (‖u‖² + ‖v‖²)`. -/
theorem block_lower_bound (A : E₁ →ₗ[𝕜] E₁) (B : E₁ →L[𝕜] E₂) (C : E₂ →ₗ[𝕜] E₂)
    {α γ b : ℝ} (hA : ∀ u, α * ‖u‖ ^ 2 ≤ re ⟪A u, u⟫_𝕜)
    (hC : ∀ v, γ * ‖v‖ ^ 2 ≤ re ⟪C v, v⟫_𝕜) (hB : ‖B‖ ≤ b) (u : E₁) (v : E₂) :
    mu α γ b * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤ blockForm A B C u v := by
  have := scalar_bound α γ b ‖u‖ ‖v‖
  have := neg_le_re_inner_apply B hB u v
  have := hA u
  have := hC v
  unfold blockForm
  nlinarith

/-- **Schur criterion, operator version** (sufficiency): `m ≤ α`, `m ≤ γ`,
`b² ≤ (α − m)(γ − m)` ⇒ `blockForm ≥ m (‖u‖² + ‖v‖²)`. -/
theorem block_lower_bound_of_schur (A : E₁ →ₗ[𝕜] E₁) (B : E₁ →L[𝕜] E₂) (C : E₂ →ₗ[𝕜] E₂)
    {α γ b m : ℝ} (hA : ∀ u, α * ‖u‖ ^ 2 ≤ re ⟪A u, u⟫_𝕜)
    (hC : ∀ v, γ * ‖v‖ ^ 2 ≤ re ⟪C v, v⟫_𝕜) (hB : ‖B‖ ≤ b)
    (hmα : m ≤ α) (hmγ : m ≤ γ) (hschur : b ^ 2 ≤ (α - m) * (γ - m)) (u : E₁) (v : E₂) :
    m * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤ blockForm A B C u v := by
  have hm := (le_mu_iff α γ b m).mpr ⟨hmα, hmγ, hschur⟩
  refine le_trans ?_ (block_lower_bound A B C hA hC hB u v)
  exact mul_le_mul_of_nonneg_right hm (by positivity)

section Adjoint

variable [CompleteSpace E₁] [CompleteSpace E₂]

/-- The block operator `H = [[A, B†], [B, C]]` on the Hilbert sum `WithLp 2 (E₁ × E₂)`. -/
noncomputable def blockOp (A : E₁ →L[𝕜] E₁) (B : E₁ →L[𝕜] E₂) (C : E₂ →L[𝕜] E₂)
    (ψ : WithLp 2 (E₁ × E₂)) : WithLp 2 (E₁ × E₂) :=
  WithLp.toLp 2 (A ψ.fst + ContinuousLinearMap.adjoint B ψ.snd, B ψ.fst + C ψ.snd)

/-- `Re⟪Hψ, ψ⟫ = blockForm A B C ψ₁ ψ₂`. -/
theorem re_inner_blockOp (A : E₁ →L[𝕜] E₁) (B : E₁ →L[𝕜] E₂) (C : E₂ →L[𝕜] E₂)
    (ψ : WithLp 2 (E₁ × E₂)) :
    re ⟪blockOp A B C ψ, ψ⟫_𝕜 = blockForm (A : E₁ →ₗ[𝕜] E₁) B (C : E₂ →ₗ[𝕜] E₂) ψ.fst ψ.snd := by
  rw [WithLp.prod_inner_apply]
  simp only [blockOp, WithLp.ofLp_toLp, WithLp.ofLp_fst, WithLp.ofLp_snd, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, map_add, blockForm, ContinuousLinearMap.coe_coe]
  rw [inner_re_symm (𝕜 := 𝕜) ψ.snd (B ψ.fst)]
  ring

/-- **Block Hamiltonian bound.** `Re⟪Hψ, ψ⟫ ≥ μ(α,γ,b) ‖ψ‖²` for `H = [[A, B†], [B, C]]`. -/
theorem blockOp_lower_bound (A : E₁ →L[𝕜] E₁) (B : E₁ →L[𝕜] E₂) (C : E₂ →L[𝕜] E₂)
    {α γ b : ℝ} (hA : ∀ u, α * ‖u‖ ^ 2 ≤ re ⟪A u, u⟫_𝕜)
    (hC : ∀ v, γ * ‖v‖ ^ 2 ≤ re ⟪C v, v⟫_𝕜) (hB : ‖B‖ ≤ b) (ψ : WithLp 2 (E₁ × E₂)) :
    mu α γ b * ‖ψ‖ ^ 2 ≤ re ⟪blockOp A B C ψ, ψ⟫_𝕜 := by
  rw [re_inner_blockOp, WithLp.prod_norm_sq_eq_of_L2]
  exact block_lower_bound _ B _ hA hC hB _ _

end Adjoint

end Operator

/-! ## 4. Hierarchies of scales -/

/-- Left Gershgorin weight at scale `i`: `0` at `i = 0`, `b_{i-1}/t_{i-1}` otherwise. -/
noncomputable def leftW (b t : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => b i / t i

/-- Right Gershgorin weight at scale `i` in the chain `0..n`: `b_i t_i` if `i < n`, else `0`. -/
noncomputable def rightW (n : ℕ) (b t : ℕ → ℝ) (i : ℕ) : ℝ := if i < n then b i * t i else 0

lemma leftW_nonneg {b t : ℕ → ℝ} (hb : ∀ i, 0 ≤ b i) (ht : ∀ i, 0 < t i) (i : ℕ) :
    0 ≤ leftW b t i := by
  cases i with
  | zero => simp [leftW]
  | succ i => exact div_nonneg (hb i) (ht i).le

lemma rightW_le {n : ℕ} {b t : ℕ → ℝ} (hb : ∀ i, 0 ≤ b i) (ht : ∀ i, 0 < t i) (i : ℕ) :
    rightW n b t i ≤ b i * t i := by
  unfold rightW; split_ifs
  · exact le_rfl
  · exact mul_nonneg (hb i) (ht i).le

/-- Weighted AM–GM: `2 b x y ≤ b t x² + (b/t) y²` for `b ≥ 0`, `t > 0`. -/
lemma two_mul_le_weighted {b t : ℝ} (hb : 0 ≤ b) (ht : 0 < t) (x y : ℝ) :
    2 * b * x * y ≤ b * t * x ^ 2 + b / t * y ^ 2 := by
  have e : b * t * x ^ 2 + b / t * y ^ 2 - 2 * b * x * y = b * (t * x - y) ^ 2 / t := by
    field_simp; ring
  have : 0 ≤ b * (t * x - y) ^ 2 / t := by positivity
  linarith

/-- **Scalar weighted Gershgorin bound for a tridiagonal chain.** -/
theorem chain_scalar (n : ℕ) (α b t x : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) (ht : ∀ i, 0 < t i)
    {m : ℝ} (hm : ∀ i ≤ n, m ≤ α i - leftW b t i - rightW n b t i) :
    m * ∑ i ∈ Finset.range (n + 1), x i ^ 2 ≤
      ∑ i ∈ Finset.range (n + 1), α i * x i ^ 2 -
        2 * ∑ i ∈ Finset.range n, b i * x i * x (i + 1) := by
  have S1 : ∑ i ∈ Finset.range n, b i * t i * x i ^ 2 =
      ∑ i ∈ Finset.range (n + 1), rightW n b t i * x i ^ 2 := by
    rw [Finset.sum_range_succ]
    simp only [rightW, lt_irrefl, ite_false, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [Finset.mem_range.mp hi]
  have S2 : ∑ i ∈ Finset.range n, b i / t i * x (i + 1) ^ 2 =
      ∑ i ∈ Finset.range (n + 1), leftW b t i * x i ^ 2 := by
    rw [Finset.sum_range_succ']
    simp [leftW]
  have amgm : 2 * ∑ i ∈ Finset.range n, b i * x i * x (i + 1) ≤
      ∑ i ∈ Finset.range n, b i * t i * x i ^ 2 +
        ∑ i ∈ Finset.range n, b i / t i * x (i + 1) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := two_mul_le_weighted (hb i) (ht i) (x i) (x (i + 1))
    linarith
  have diag : m * ∑ i ∈ Finset.range (n + 1), x i ^ 2 ≤
      ∑ i ∈ Finset.range (n + 1), (α i - leftW b t i - rightW n b t i) * x i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_right
      (hm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) (sq_nonneg _)
  have expand : ∑ i ∈ Finset.range (n + 1), (α i - leftW b t i - rightW n b t i) * x i ^ 2 =
      ∑ i ∈ Finset.range (n + 1), α i * x i ^ 2 -
        ∑ i ∈ Finset.range (n + 1), leftW b t i * x i ^ 2 -
        ∑ i ∈ Finset.range (n + 1), rightW n b t i * x i ^ 2 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  linarith

section Chain

variable {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)]

/-- Quadratic form of the tridiagonal block operator on scales `0..n`:
`Σ_{i≤n} Re⟪A_i u_i, u_i⟫ + 2 Σ_{i<n} Re⟪B_i u_i, u_{i+1}⟫`. -/
noncomputable def chainForm (A : ∀ i, E i →ₗ[𝕜] E i) (B : ∀ i, E i →L[𝕜] E (i + 1))
    (n : ℕ) (u : ∀ i, E i) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), re ⟪A i (u i), u i⟫_𝕜 +
    2 * ∑ i ∈ Finset.range n, re ⟪B i (u i), u (i + 1)⟫_𝕜

/-- **Weighted Gershgorin bound for a finite hierarchy of scales.** Diagonal bounds
`Re⟪A_i u,u⟫ ≥ α_i‖u‖²`, couplings `‖B_i‖ ≤ b_i`, weights `t_i > 0` and
`m ≤ α_i − b_{i−1}/t_{i−1} − b_i t_i` (end terms omitted) for `i ≤ n`
⇒ `chainForm ≥ m Σ_{i≤n} ‖u_i‖²`. -/
theorem chain_lower_bound (A : ∀ i, E i →ₗ[𝕜] E i) (B : ∀ i, E i →L[𝕜] E (i + 1))
    (α b t : ℕ → ℝ) (hA : ∀ i (w : E i), α i * ‖w‖ ^ 2 ≤ re ⟪A i w, w⟫_𝕜)
    (hB : ∀ i, ‖B i‖ ≤ b i) (ht : ∀ i, 0 < t i) {n : ℕ} {m : ℝ}
    (hm : ∀ i ≤ n, m ≤ α i - leftW b t i - rightW n b t i) (u : ∀ i, E i) :
    m * ∑ i ∈ Finset.range (n + 1), ‖u i‖ ^ 2 ≤ chainForm A B n u := by
  have hb : ∀ i, 0 ≤ b i := fun i => (norm_nonneg _).trans (hB i)
  have hs := chain_scalar n α b t (fun i => ‖u i‖) hb ht hm
  have h1 : ∑ i ∈ Finset.range (n + 1), α i * ‖u i‖ ^ 2 ≤
      ∑ i ∈ Finset.range (n + 1), re ⟪A i (u i), u i⟫_𝕜 :=
    Finset.sum_le_sum fun i _ => hA i (u i)
  have h2 : -∑ i ∈ Finset.range n, b i * ‖u i‖ * ‖u (i + 1)‖ ≤
      ∑ i ∈ Finset.range n, re ⟪B i (u i), u (i + 1)⟫_𝕜 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => neg_le_re_inner_apply (B i) (hB i) _ _
  unfold chainForm
  linarith

@[simp] lemma leftW_one_succ (b : ℕ → ℝ) (i : ℕ) : leftW b (fun _ => 1) (i + 1) = b i := by
  simp [leftW]

/-- **Unweighted Gershgorin bound** (`t ≡ 1`): `m ≤ α_i − b_{i−1} − b_i` (end terms omitted). -/
theorem chain_lower_bound_gershgorin (A : ∀ i, E i →ₗ[𝕜] E i) (B : ∀ i, E i →L[𝕜] E (i + 1))
    (α b : ℕ → ℝ) (hA : ∀ i (w : E i), α i * ‖w‖ ^ 2 ≤ re ⟪A i w, w⟫_𝕜)
    (hB : ∀ i, ‖B i‖ ≤ b i) {n : ℕ} {m : ℝ}
    (hm : ∀ i ≤ n, m ≤ α i - leftW b (fun _ => 1) i - rightW n b (fun _ => 1) i)
    (u : ∀ i, E i) :
    m * ∑ i ∈ Finset.range (n + 1), ‖u i‖ ^ 2 ≤ chainForm A B n u :=
  chain_lower_bound A B α b (fun _ => 1) hA hB (fun _ => one_pos) hm u

/-- **Uniform bounds**: `α_i ≥ α`, `‖B_i‖ ≤ b` for all `i` ⇒ `chainForm ≥ (α − 2b) Σ ‖u_i‖²`. -/
theorem chain_lower_bound_uniform (A : ∀ i, E i →ₗ[𝕜] E i) (B : ∀ i, E i →L[𝕜] E (i + 1))
    {α b : ℝ} (hA : ∀ i (w : E i), α * ‖w‖ ^ 2 ≤ re ⟪A i w, w⟫_𝕜)
    (hB : ∀ i, ‖B i‖ ≤ b) (n : ℕ) (u : ∀ i, E i) :
    (α - 2 * b) * ∑ i ∈ Finset.range (n + 1), ‖u i‖ ^ 2 ≤ chainForm A B n u := by
  have hb : 0 ≤ b := (norm_nonneg _).trans (hB 0)
  refine chain_lower_bound A B (fun _ => α) (fun _ => b) (fun _ => 1) hA hB
    (fun _ => one_pos) (fun i _ => ?_) u
  have h1 : leftW (fun _ => b) (fun _ => (1:ℝ)) i ≤ b := by
    cases i with
    | zero => simp [leftW, hb]
    | succ i => simp [leftW]
  have h2 := rightW_le (n := n) (fun _ => hb) (fun _ => one_pos) i
  simp only [mul_one] at h2
  linarith

/-! ### Infinite hierarchy on finitely supported families -/

/-- The truncated form stabilises: if `u_i = 0` for `i > N`, then `chainForm M u = chainForm N u`
for all `M ≥ N`. Hence `chainForm` is well defined on finitely supported families. -/
theorem chainForm_stable (A : ∀ i, E i →ₗ[𝕜] E i) (B : ∀ i, E i →L[𝕜] E (i + 1))
    {u : ∀ i, E i} {N : ℕ} (hu : ∀ i, N < i → u i = 0) {M : ℕ} (hM : N ≤ M) :
    chainForm A B M u = chainForm A B N u := by
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    rw [← ih]
    have h1 : u (M + 1) = 0 := hu _ (by omega)
    have hA' : ∑ i ∈ Finset.range (M + 1 + 1), re ⟪A i (u i), u i⟫_𝕜 =
        ∑ i ∈ Finset.range (M + 1), re ⟪A i (u i), u i⟫_𝕜 := by
      rw [Finset.sum_range_succ, h1]; simp
    have hB' : ∑ i ∈ Finset.range (M + 1), re ⟪B i (u i), u (i + 1)⟫_𝕜 =
        ∑ i ∈ Finset.range M, re ⟪B i (u i), u (i + 1)⟫_𝕜 := by
      rw [Finset.sum_range_succ, h1]; simp
    unfold chainForm
    rw [hA', hB']

theorem normSum_stable {u : ∀ i, E i} {N : ℕ} (hu : ∀ i, N < i → u i = 0) {M : ℕ}
    (hM : N ≤ M) :
    ∑ i ∈ Finset.range (M + 1), ‖u i‖ ^ 2 = ∑ i ∈ Finset.range (N + 1), ‖u i‖ ^ 2 := by
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    rw [Finset.sum_range_succ, ih, hu _ (by omega)]
    simp

/-- **Infinite hierarchy (weighted).** Scales `i ∈ ℕ`; hypotheses for *all* `i`:
`Re⟪A_i u,u⟫ ≥ α_i‖u‖²`, `‖B_i‖ ≤ b_i`, `t_i > 0`, `m ≤ α_i − b_{i−1}/t_{i−1} − b_i t_i`.
Domain: finitely supported families (`u_i = 0` for `i > N`). Then for every truncation
`M ≥ N` (all giving the same value, `chainForm_stable`), `chainForm M u ≥ m Σ_i ‖u_i‖²`. -/
theorem hierarchy_lower_bound (A : ∀ i, E i →ₗ[𝕜] E i) (B : ∀ i, E i →L[𝕜] E (i + 1))
    (α b t : ℕ → ℝ) (hA : ∀ i (w : E i), α i * ‖w‖ ^ 2 ≤ re ⟪A i w, w⟫_𝕜)
    (hB : ∀ i, ‖B i‖ ≤ b i) (ht : ∀ i, 0 < t i) {m : ℝ}
    (hm : ∀ i, m ≤ α i - leftW b t i - b i * t i)
    {u : ∀ i, E i} {N : ℕ} (hu : ∀ i, N < i → u i = 0) {M : ℕ} (hM : N ≤ M) :
    m * ∑ i ∈ Finset.range (N + 1), ‖u i‖ ^ 2 ≤ chainForm A B M u := by
  have hb : ∀ i, 0 ≤ b i := fun i => (norm_nonneg _).trans (hB i)
  rw [← normSum_stable hu hM]
  refine chain_lower_bound A B α b t hA hB ht (fun i _ => ?_) u
  have := rightW_le (n := M) hb ht i
  linarith [hm i]

/-- **Infinite hierarchy, sup bounds.** `inf_i α_i ≥ α` and `sup_i ‖B_i‖ ≤ b` ⇒
`chainForm ≥ (α − 2b) Σ ‖u_i‖²` on finitely supported families. -/
theorem hierarchy_lower_bound_uniform (A : ∀ i, E i →ₗ[𝕜] E i) (B : ∀ i, E i →L[𝕜] E (i + 1))
    {α b : ℝ} (hA : ∀ i (w : E i), α * ‖w‖ ^ 2 ≤ re ⟪A i w, w⟫_𝕜)
    (hB : ∀ i, ‖B i‖ ≤ b) {u : ∀ i, E i} {N : ℕ} (hu : ∀ i, N < i → u i = 0) {M : ℕ}
    (hM : N ≤ M) :
    (α - 2 * b) * ∑ i ∈ Finset.range (N + 1), ‖u i‖ ^ 2 ≤ chainForm A B M u := by
  rw [← normSum_stable hu hM]
  exact chain_lower_bound_uniform A B hA hB M u

end Chain

/-! ## 5. Transfer-matrix application (abstract) -/

section Transfer

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Generator bound ⇒ transfer bound.** For any linear `T` on an inner product space and a
set `S` of vectors (e.g. `Ω^⊥`): if `Re⟪(I − T)ψ, ψ⟫ / a ≥ Δ‖ψ‖²` on `S` (`a > 0`) then
`Re⟪Tψ, ψ⟫ ≤ (1 − aΔ)‖ψ‖² ≤ e^{−aΔ}‖ψ‖²` on `S`. -/
theorem transfer_of_generator_bound {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (T : F →ₗ[𝕜] F) {a Δ : ℝ} (ha : 0 < a) (S : Set F)
    (h : ∀ ψ ∈ S, Δ * ‖ψ‖ ^ 2 ≤ re ⟪ψ - T ψ, ψ⟫_𝕜 / a) {ψ : F} (hψ : ψ ∈ S) :
    re ⟪T ψ, ψ⟫_𝕜 ≤ (1 - a * Δ) * ‖ψ‖ ^ 2 ∧
      (1 - a * Δ) * ‖ψ‖ ^ 2 ≤ Real.exp (-(a * Δ)) * ‖ψ‖ ^ 2 := by
  have h1 := h ψ hψ
  rw [le_div_iff₀ ha, inner_sub_left, map_sub, inner_self_eq_norm_sq] at h1
  refine ⟨by nlinarith, mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)⟩
  linarith [Real.add_one_le_exp (-(a * Δ))]

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]

/-- **Block generator ⇒ transfer bound.** Let `T` act on `WithLp 2 (E₁ × E₂)` and suppose
that on a set `S` the generator `(I − T)/a` has the block quadratic form
`Re⟪(I − T)ψ, ψ⟫ = a · blockForm A B C ψ₁ ψ₂`, where `Re⟪Au,u⟫ ≥ α‖u‖²`, `Re⟪Cv,v⟫ ≥ γ‖v‖²`,
`‖B‖ ≤ b`, and `Δ ≤ μ(α,γ,b)`. Then `Re⟪Tψ, ψ⟫ ≤ e^{−aΔ}‖ψ‖²` on `S`.

**Caveat.** Uniformity of `α, γ, b` (hence of `Δ`) in the lattice spacing `a` and the volume
`L` is a HYPOTHESIS here; it is not derived from Yang–Mills. Moreover, if `T` is not the
Osterwalder–Schrader transfer matrix (e.g. `(I − T)/a` is the generator of an auxiliary
stochastic dynamics), a gap for it is not the gap of the quantum Hamiltonian. -/
theorem transfer_of_block_generator (T : WithLp 2 (E₁ × E₂) →ₗ[𝕜] WithLp 2 (E₁ × E₂))
    (A : E₁ →ₗ[𝕜] E₁) (B : E₁ →L[𝕜] E₂) (C : E₂ →ₗ[𝕜] E₂)
    {α γ b a Δ : ℝ} (ha : 0 < a) (hA : ∀ u, α * ‖u‖ ^ 2 ≤ re ⟪A u, u⟫_𝕜)
    (hC : ∀ v, γ * ‖v‖ ^ 2 ≤ re ⟪C v, v⟫_𝕜) (hB : ‖B‖ ≤ b) (hΔ : Δ ≤ mu α γ b)
    (S : Set (WithLp 2 (E₁ × E₂)))
    (hgen : ∀ ψ ∈ S, re ⟪ψ - T ψ, ψ⟫_𝕜 = a * blockForm A B C ψ.fst ψ.snd)
    {ψ : WithLp 2 (E₁ × E₂)} (hψ : ψ ∈ S) :
    re ⟪T ψ, ψ⟫_𝕜 ≤ Real.exp (-(a * Δ)) * ‖ψ‖ ^ 2 := by
  have key : ∀ φ ∈ S, Δ * ‖φ‖ ^ 2 ≤ re ⟪φ - T φ, φ⟫_𝕜 / a := by
    intro φ hφ
    rw [hgen φ hφ, mul_div_cancel_left₀ _ ha.ne', WithLp.prod_norm_sq_eq_of_L2]
    refine le_trans ?_ (block_lower_bound A B C hA hC hB _ _)
    exact mul_le_mul_of_nonneg_right hΔ (by positivity)
  have := transfer_of_generator_bound T ha S key hψ
  exact this.1.trans this.2

/-- Eigenvalue form: under the hypotheses of `transfer_of_block_generator`, every real
eigenvalue `λ` of `T` with an eigenvector in `S` satisfies `λ ≤ 1 − aΔ ≤ e^{−aΔ}`. (With `S =
Ω^⊥` this is the upper half of the hypothesis `hspec` of `APEX.YM.transfer_bound`.) -/
theorem eigenvalue_le_of_block_generator (T : WithLp 2 (E₁ × E₂) →ₗ[𝕜] WithLp 2 (E₁ × E₂))
    (A : E₁ →ₗ[𝕜] E₁) (B : E₁ →L[𝕜] E₂) (C : E₂ →ₗ[𝕜] E₂)
    {α γ b a Δ : ℝ} (ha : 0 < a) (hA : ∀ u, α * ‖u‖ ^ 2 ≤ re ⟪A u, u⟫_𝕜)
    (hC : ∀ v, γ * ‖v‖ ^ 2 ≤ re ⟪C v, v⟫_𝕜) (hB : ‖B‖ ≤ b) (hΔ : Δ ≤ mu α γ b)
    (S : Set (WithLp 2 (E₁ × E₂)))
    (hgen : ∀ ψ ∈ S, re ⟪ψ - T ψ, ψ⟫_𝕜 = a * blockForm A B C ψ.fst ψ.snd)
    {v : WithLp 2 (E₁ × E₂)} (hv : v ∈ S) (hv0 : v ≠ 0) {l : ℝ} (hTv : T v = (l : 𝕜) • v) :
    l ≤ Real.exp (-(a * Δ)) := by
  have h := transfer_of_block_generator T A B C ha hA hC hB hΔ S hgen hv
  rw [hTv, inner_smul_left, conj_ofReal, re_ofReal_mul, inner_self_eq_norm_sq] at h
  have hn : 0 < ‖v‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right h hn

end Transfer

end APEX.YM.BlockGap

