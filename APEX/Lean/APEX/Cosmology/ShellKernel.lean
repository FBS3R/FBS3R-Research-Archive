import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

/-!
# Shell observation kernel (MISSION-12, first exact layer)

All results here are classical linear algebra (KNOWN_RESULT); this file is a formalization layer.

Setting: in angular sector `l`, the radial profile of a mode is `(sin χ)^l * p(cos χ)` with
`p ∈ degreeLT ℝ (d+1)` (real polynomials of degree `≤ d`). Observing on `q` pairwise distinct
shells `χ i ∈ (0, π)` is the linear map `shellObs l d χ : degreeLT ℝ (d+1) →ₗ[ℝ] (Fin q → ℝ)`,
`p ↦ (i ↦ (sin (χ i))^l * p.eval (cos (χ i)))`.

Proved:
* `obs_zero_iff`: for distinct `χ i ∈ (0,π)` and any `p : ℝ[X]`,
  `(∀ i, sin (χ i)^l * p.eval (cos (χ i)) = 0) ↔ (∏ i, (X - C (cos (χ i)))) ∣ p`.
* `mem_ker_shellObs`: the kernel of `shellObs` is exactly the multiples of the nodal polynomial.
* `shellObs_injective`: injective when `d + 1 ≤ q`.
* `shellObs_surjective`: surjective when `q ≤ d + 1`.
* `finrank_ker_shellObs`: `finrank (ker) = d + 1 - q` (natural subtraction: so `= 0` when `q ≥ d+1`).
* `finrank_range_shellObs`: `finrank (range) = min q (d+1)` (full rank).
* `shellObs_injective_iff` (reconstruction criterion): injective ↔ `d + 1 ≤ q`.
* `nonident_same_data`, `nonident_eq_iff`, `nonident_eventually_pos`: abstract non-identifiability
  for `M : ℝ → Matrix (Fin N) (Fin N) ℝ`, `P χ := (M χ)⁻¹ * M χ₀ * P₀`.

Lagrange interpolation / Vandermonde files of Mathlib are not built in this environment, so the
surjectivity is derived from injectivity on `degreeLT ℝ q` plus a dimension count
(`Polynomial.degreeLTEquiv`) instead.
-/

open Polynomial Real Module

namespace APEX.Cosmology

noncomputable section

/-- `degreeLT ℝ n` is finite-dimensional (via `degreeLTEquiv`). -/
instance degreeLT_finite (n : ℕ) : Module.Finite ℝ (degreeLT ℝ n) :=
  Module.Finite.equiv (degreeLTEquiv ℝ n).symm

theorem finrank_degreeLT' (n : ℕ) : finrank ℝ (degreeLT ℝ n) = n := by
  rw [(degreeLTEquiv ℝ n).finrank_eq]; simp

/-- Pure evaluation at nodes `c i` on `degreeLT ℝ n`. -/
def evalObs {q : ℕ} (n : ℕ) (c : Fin q → ℝ) : degreeLT ℝ n →ₗ[ℝ] (Fin q → ℝ) where
  toFun p i := (p : ℝ[X]).eval (c i)
  map_add' p p' := by ext i; simp
  map_smul' a p := by ext i; simp [smul_eq_C_mul]

@[simp] theorem evalObs_apply {q n : ℕ} (c : Fin q → ℝ) (p : degreeLT ℝ n) (i : Fin q) :
    evalObs n c p i = (p : ℝ[X]).eval (c i) := rfl

/-- The shell observation map in angular sector `l`. -/
def shellObs {q : ℕ} (l d : ℕ) (χ : Fin q → ℝ) : degreeLT ℝ (d + 1) →ₗ[ℝ] (Fin q → ℝ) where
  toFun p i := sin (χ i) ^ l * (p : ℝ[X]).eval (cos (χ i))
  map_add' p p' := by ext i; simp [mul_add]
  map_smul' a p := by ext i; simp [smul_eq_C_mul]; ring

@[simp] theorem shellObs_apply {q : ℕ} (l d : ℕ) (χ : Fin q → ℝ) (p : degreeLT ℝ (d + 1))
    (i : Fin q) : shellObs l d χ p i = sin (χ i) ^ l * (p : ℝ[X]).eval (cos (χ i)) := rfl

/-- Hypothesis bundle: shells are pairwise distinct and non-polar. -/
def GoodShells {q : ℕ} (χ : Fin q → ℝ) : Prop :=
  Function.Injective χ ∧ ∀ i, 0 < χ i ∧ χ i < π

theorem GoodShells.cos_injective {q : ℕ} {χ : Fin q → ℝ} (h : GoodShells χ) :
    Function.Injective (fun i => cos (χ i)) := by
  intro i j hij
  apply h.1
  exact injOn_cos ⟨(h.2 i).1.le, (h.2 i).2.le⟩ ⟨(h.2 j).1.le, (h.2 j).2.le⟩ hij

theorem GoodShells.sin_pow_ne_zero {q : ℕ} {χ : Fin q → ℝ} (h : GoodShells χ) (l : ℕ)
    (i : Fin q) : sin (χ i) ^ l ≠ 0 :=
  pow_ne_zero _ (sin_pos_of_pos_of_lt_pi (h.2 i).1 (h.2 i).2).ne'

/-- Vanishing at distinct nodes ↔ divisibility by the nodal polynomial. -/
theorem eval_zero_iff_nodal_dvd {q : ℕ} {c : Fin q → ℝ} (hc : Function.Injective c) (p : ℝ[X]) :
    (∀ i, p.eval (c i) = 0) ↔ (∏ i, (X - C (c i))) ∣ p := by
  have hprod : (∏ i, (X - C (c i))) =
      ((Finset.univ.val.map c).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  have hnd : (Finset.univ.val.map c).Nodup := (Finset.univ.nodup).map hc
  constructor
  · intro h
    by_cases hp : p = 0
    · simp [hp]
    rw [hprod, Multiset.prod_X_sub_C_dvd_iff_le_roots hp, Multiset.le_iff_subset hnd]
    intro a ha
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
    exact (mem_roots hp).2 (h i)
  · rintro ⟨r, rfl⟩ i
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp), zero_mul]

/-- **obs_zero_iff** (KNOWN_RESULT). -/
theorem obs_zero_iff {q : ℕ} (l : ℕ) {χ : Fin q → ℝ} (h : GoodShells χ) (p : ℝ[X]) :
    (∀ i, sin (χ i) ^ l * p.eval (cos (χ i)) = 0) ↔ (∏ i, (X - C (cos (χ i)))) ∣ p := by
  rw [← eval_zero_iff_nodal_dvd h.cos_injective p]
  exact forall_congr' fun i => by simp [h.sin_pow_ne_zero l i]

/-- Kernel of the shell observation map = multiples of the nodal polynomial. -/
theorem mem_ker_shellObs {q : ℕ} (l d : ℕ) {χ : Fin q → ℝ} (h : GoodShells χ)
    (p : degreeLT ℝ (d + 1)) :
    p ∈ LinearMap.ker (shellObs l d χ) ↔ (∏ i, (X - C (cos (χ i)))) ∣ (p : ℝ[X]) := by
  rw [LinearMap.mem_ker, ← obs_zero_iff l h, funext_iff]; rfl

theorem ker_shellObs_eq {q : ℕ} (l d : ℕ) {χ : Fin q → ℝ} (h : GoodShells χ) :
    LinearMap.ker (shellObs l d χ) = LinearMap.ker (evalObs (d + 1) (fun i => cos (χ i))) := by
  ext p
  simp only [LinearMap.mem_ker, funext_iff, shellObs_apply, evalObs_apply, Pi.zero_apply]
  exact forall_congr' fun i => by simp [h.sin_pow_ne_zero l i]

theorem evalObs_injective {q n : ℕ} {c : Fin q → ℝ} (hc : Function.Injective c) (hn : n ≤ q) :
    Function.Injective (evalObs n c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  have hev : ∀ i, (p : ℝ[X]).eval (c i) = 0 := fun i => congrFun hp i
  ext1
  show (p : ℝ[X]) = 0
  by_contra hne
  have hdeg := mem_degreeLT.1 p.2
  rw [← natDegree_lt_iff_degree_lt hne] at hdeg
  exact hne (eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hc hev
    (by simpa using hdeg.trans_le hn))

theorem evalObs_surjective {q n : ℕ} {c : Fin q → ℝ} (hc : Function.Injective c) (hn : q ≤ n) :
    Function.Surjective (evalObs n c) := by
  have hq : Function.Surjective (evalObs q c) := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_degreeLT']; simp)]
    exact evalObs_injective hc le_rfl
  intro y
  obtain ⟨p, hp⟩ := hq y
  exact ⟨Submodule.inclusion (degreeLT_mono hn) p, by rw [← hp]; rfl⟩

/-- Injectivity of the shell map when `q ≥ d + 1` (KNOWN_RESULT). -/
theorem shellObs_injective {q : ℕ} (l d : ℕ) {χ : Fin q → ℝ} (h : GoodShells χ)
    (hq : d + 1 ≤ q) : Function.Injective (shellObs l d χ) := by
  rw [← LinearMap.ker_eq_bot, ker_shellObs_eq l d h, LinearMap.ker_eq_bot]
  exact evalObs_injective h.cos_injective hq

/-- Surjectivity of the shell map when `q ≤ d + 1` (KNOWN_RESULT). -/
theorem shellObs_surjective {q : ℕ} (l d : ℕ) {χ : Fin q → ℝ} (h : GoodShells χ)
    (hq : q ≤ d + 1) : Function.Surjective (shellObs l d χ) := by
  intro y
  obtain ⟨p, hp⟩ := evalObs_surjective (n := d + 1) h.cos_injective hq
    (fun i => y i / sin (χ i) ^ l)
  refine ⟨p, funext fun i => ?_⟩
  have := congrFun hp i
  simp only [evalObs_apply] at this
  simp only [shellObs_apply, this]
  field_simp [h.sin_pow_ne_zero l i]

/-- Kernel dimension `d + 1 - q` (truncated subtraction; `0` when `q ≥ d+1`) (KNOWN_RESULT). -/
theorem finrank_ker_shellObs {q : ℕ} (l d : ℕ) {χ : Fin q → ℝ} (h : GoodShells χ) :
    finrank ℝ (LinearMap.ker (shellObs l d χ)) = d + 1 - q := by
  rcases le_total q (d + 1) with hq | hq
  · have hrn := LinearMap.finrank_range_add_finrank_ker (shellObs l d χ)
    rw [LinearMap.range_eq_top.2 (shellObs_surjective l d h hq), finrank_top,
      finrank_degreeLT'] at hrn
    simp at hrn
    omega
  · rw [LinearMap.ker_eq_bot.2 (shellObs_injective l d h hq), finrank_bot]
    omega

/-- The kernel is `{0}` when `q ≥ d + 1`. -/
theorem ker_shellObs_eq_bot {q : ℕ} (l d : ℕ) {χ : Fin q → ℝ} (h : GoodShells χ)
    (hq : d + 1 ≤ q) : LinearMap.ker (shellObs l d χ) = ⊥ :=
  LinearMap.ker_eq_bot.2 (shellObs_injective l d h hq)

/-- Full rank: `rank = min q (d+1)` (KNOWN_RESULT). -/
theorem finrank_range_shellObs {q : ℕ} (l d : ℕ) {χ : Fin q → ℝ} (h : GoodShells χ) :
    finrank ℝ (LinearMap.range (shellObs l d χ)) = min q (d + 1) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (shellObs l d χ)
  rw [finrank_ker_shellObs l d h, finrank_degreeLT'] at hrn
  omega

/-- **Reconstruction criterion** (KNOWN_RESULT): degree-`≤ d` profiles are uniquely determined by
the `q` shell observations iff `q ≥ d + 1`. -/
theorem shellObs_injective_iff {q : ℕ} (l d : ℕ) {χ : Fin q → ℝ} (h : GoodShells χ) :
    Function.Injective (shellObs l d χ) ↔ d + 1 ≤ q := by
  refine ⟨fun hinj => ?_, shellObs_injective l d h⟩
  by_contra hlt
  have := finrank_ker_shellObs l d h
  rw [LinearMap.ker_eq_bot.2 hinj, finrank_bot] at this
  omega

/-! ## Abstract non-identifiability (KNOWN_RESULT) -/

section NonIdent

variable {N K : ℕ}

/-- Compensating parameter: `P χ := (M χ)⁻¹ * M χ₀ * P₀`. -/
def compensate (M : ℝ → Matrix (Fin N) (Fin N) ℝ) (χ₀ : ℝ) (P₀ : Matrix (Fin N) (Fin K) ℝ)
    (χ : ℝ) : Matrix (Fin N) (Fin K) ℝ :=
  (M χ)⁻¹ * M χ₀ * P₀

/-- Same observed data: `M χ * P χ = M χ₀ * P₀` whenever `M χ` is invertible. -/
theorem nonident_same_data (M : ℝ → Matrix (Fin N) (Fin N) ℝ) (χ₀ : ℝ)
    (P₀ : Matrix (Fin N) (Fin K) ℝ) {χ : ℝ} (hχ : IsUnit (M χ).det) :
    M χ * compensate M χ₀ P₀ χ = M χ₀ * P₀ := by
  unfold compensate
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hχ]

/-- `P χ = P₀` iff `M χ` already reproduces the data with `P₀`. -/
theorem nonident_eq_iff (M : ℝ → Matrix (Fin N) (Fin N) ℝ) (χ₀ : ℝ)
    (P₀ : Matrix (Fin N) (Fin K) ℝ) {χ : ℝ} (hχ : IsUnit (M χ).det) :
    compensate M χ₀ P₀ χ = P₀ ↔ M χ * P₀ = M χ₀ * P₀ := by
  constructor
  · intro he; rw [← nonident_same_data M χ₀ P₀ hχ, he]
  · intro he
    unfold compensate
    rw [Matrix.mul_assoc, ← he, Matrix.nonsing_inv_mul_cancel_left _ _ hχ]

/-- Positivity persists: if `M χ₀` is invertible, `P₀` has strictly positive entries and
`χ ↦ (M χ)⁻¹` is continuous at `χ₀`, then for all `χ` in a neighbourhood of `χ₀` the compensating
parameter has strictly positive entries and (where `M χ` is invertible) gives the same data. -/
theorem nonident_eventually_pos (M : ℝ → Matrix (Fin N) (Fin N) ℝ) (χ₀ : ℝ)
    (P₀ : Matrix (Fin N) (Fin K) ℝ) (h₀ : IsUnit (M χ₀).det) (hpos : ∀ i j, 0 < P₀ i j)
    (hcont : ContinuousAt (fun χ => (M χ)⁻¹) χ₀) :
    ∀ᶠ χ in nhds χ₀, ∀ i j, 0 < compensate M χ₀ P₀ χ i j := by
  have hP : ContinuousAt (compensate M χ₀ P₀) χ₀ := by
    have hc : Continuous fun A : Matrix (Fin N) (Fin N) ℝ => A * M χ₀ * P₀ :=
      (continuous_id.matrix_mul continuous_const).matrix_mul continuous_const
    exact hc.continuousAt.comp hcont
  have hP0 : compensate M χ₀ P₀ χ₀ = P₀ := by
    unfold compensate; rw [Matrix.nonsing_inv_mul _ h₀, Matrix.one_mul]
  have hopen : IsOpen {A : Matrix (Fin N) (Fin K) ℝ | ∀ i j, 0 < A i j} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const ((continuous_apply j).comp (continuous_apply i))
  have hmem : compensate M χ₀ P₀ χ₀ ∈ {A : Matrix (Fin N) (Fin K) ℝ | ∀ i j, 0 < A i j} := by
    rw [hP0]; exact hpos
  exact hP.preimage_mem_nhds (hopen.mem_nhds hmem)

/-- Combined: near `χ₀`, every `χ` with `M χ` invertible yields a strictly positive parameter
reproducing exactly the data `M χ₀ * P₀`. -/
theorem nonident_local (M : ℝ → Matrix (Fin N) (Fin N) ℝ) (χ₀ : ℝ)
    (P₀ : Matrix (Fin N) (Fin K) ℝ) (hinv : ∀ χ, IsUnit (M χ).det) (hpos : ∀ i j, 0 < P₀ i j)
    (hcont : ContinuousAt (fun χ => (M χ)⁻¹) χ₀) :
    ∀ᶠ χ in nhds χ₀, (∀ i j, 0 < compensate M χ₀ P₀ χ i j) ∧
      M χ * compensate M χ₀ P₀ χ = M χ₀ * P₀ :=
  (nonident_eventually_pos M χ₀ P₀ (hinv χ₀) hpos hcont).mono fun χ hχ =>
    ⟨hχ, nonident_same_data M χ₀ P₀ (hinv χ)⟩

end NonIdent

end

end APEX.Cosmology

