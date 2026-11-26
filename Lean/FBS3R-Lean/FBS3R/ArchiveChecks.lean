/-
# Further machine checks across the archive

* *Hierarchical Bethe-Type States on Fibonacci Graphs over S³* (2026-04-21):
  - **error found**: with `F₁ = 3, F₂ = 5`, the Binet formula of Thm `thm:scaling`,
    `F_n = (φ^{n+2} − ψ^{n+2})/√5`, is off by one: it gives `2` at `n = 1`.  Correct:
    `F_n = Fib(n+3) = (φ^{n+3} − ψ^{n+3})/√5`;
  - Cor. `cor:zero` (zero-mode multiplicity `≥ F_{n−1} − 1` in the maximally coupled model)
    is verified: the kernel of `[[A, 𝟙𝟙ᵀ], [𝟙𝟙ᵀ, 0]]` has dimension `≥ k − 1`.
* *Hopf-Lifted Ricci-Type Flow on S³* (2026-07-02), Berger family: the paper's scalar
  curvature, `|Ric|²`, `|Rm|²` (via the 3-D identity `|Rm|² = 4|Ric|² − R²`), the
  `c → 0` limit `64/a⁴`, and the ratio equation `u̇ = 8u(1−u)/x` are consistent and verified.
* *Local Balancing and Branch Decoherence in Projected GHZ Resources* (2026-05-02):
  design factorization `V = 2cs|Γ|/(c²A+s²B) = q·2r/(1+r²) = q/cosh(ln r)`,
  `V ≤ q`, equality iff `r = 1`.
* *Finite Dilation Algebra of Round Euclidean B⁴/S³ Valuation Profiles* (2026-08-10):
  homogeneous work identity `p = −ε − (A/3)ε'`; `A^n` is a `D = A d/dA` eigenfunction with
  eigenvalue `n`; the integer roots of `P_val(z) = (z−1)z(z+1)(z+2)(z+3)` are exactly
  `{1,0,−1,−2,−3}` and match the exponents of the round valuation density.
* *Trace-Free Gravity and Horizon Capacity* (2026-08-12): vacuum-energy kernel
  `P_tr(T − ρ₀ g) = P_tr(T)` for any invertible 4×4 metric, and the de Sitter capacity map
  `Λ = 3/R², R = ℓ√(q/π) ⇒ Λ = 3π/(qℓ²)`.
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace FBS3R.Checks

open Real

/-! ## Hierarchical Bethe graphs -/

/-- Shifted Fibonacci sequence with `F₁ = 3`, `F₂ = 5` (and `F₀ = 2`). -/
def F : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | n + 2 => F (n + 1) + F n

theorem F_eq_fib : ∀ n, F n = Nat.fib (n + 3)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    have e : F (n + 2) = F (n + 1) + F n := rfl
    rw [e, F_eq_fib (n + 1), F_eq_fib n, show n + 2 + 3 = n + 3 + 2 from rfl,
      Nat.fib_add_two (n := n + 3)]
    ring_nf

/-- Correct Binet formula: exponent `n + 3`. -/
theorem F_binet (n : ℕ) : (F n : ℝ) = (goldenRatio ^ (n + 3) - goldenConj ^ (n + 3)) / √5 := by
  rw [F_eq_fib, coe_fib_eq]

/-- The paper's formula (exponent `n + 2`) is wrong: at `n = 1` it gives `2`, not `F₁ = 3`. -/
theorem paper_binet_wrong :
    (goldenRatio ^ (1 + 2) - goldenConj ^ (1 + 2)) / √5 = 2 ∧ F 1 = 3 := by
  refine ⟨?_, rfl⟩
  rw [← coe_fib_eq]; norm_num [Nat.fib_add_two]

section ZeroModes

open Matrix

variable {m k : ℕ}

/-- Maximally coupled block adjacency `[[A, 𝟙𝟙ᵀ], [𝟙𝟙ᵀ, 0]]`. -/
def blockAdj (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) ℝ :=
  Matrix.fromBlocks A (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => 1) 0

theorem zero_mode (A : Matrix (Fin m) (Fin m) ℝ) (y : Fin k → ℝ) (hy : ∑ j, y j = 0) :
    blockAdj (k := k) A *ᵥ Sum.elim 0 y = 0 := by
  rw [blockAdj, Matrix.fromBlocks_mulVec]
  funext i
  rcases i with i | i <;>
    simp [Matrix.mulVec, dotProduct, Function.comp_def, hy]

/-- **Zero-mode multiplicity bound**: `dim ker ≥ k − 1`. -/
theorem zero_mode_multiplicity (A : Matrix (Fin m) (Fin m) ℝ) :
    k - 1 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (blockAdj (k := k) A))) := by
  -- the sum functional and its kernel
  let σ : (Fin k → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun y => ∑ j, y j
      map_add' := fun _ _ => by simp [Finset.sum_add_distrib]
      map_smul' := fun _ _ => by simp [Finset.mul_sum] }
  have hrank : Module.finrank ℝ (LinearMap.ker σ) + 1 ≥ k := by
    have := LinearMap.finrank_range_add_finrank_ker σ
    have hr : Module.finrank ℝ (LinearMap.range σ) ≤ 1 := by
      calc Module.finrank ℝ (LinearMap.range σ) ≤ Module.finrank ℝ ℝ :=
            Submodule.finrank_le _
        _ = 1 := Module.finrank_self ℝ
    simp only [Module.finrank_fin_fun] at this
    omega
  let ι : LinearMap.ker σ →ₗ[ℝ] LinearMap.ker (Matrix.toLin' (blockAdj (k := k) A)) :=
    { toFun := fun y => ⟨Sum.elim 0 y.1, by
        simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
        exact zero_mode A y.1 y.2⟩
      map_add' := fun a b => by
        ext i; rcases i with i | i <;> simp
      map_smul' := fun c a => by
        ext i; rcases i with i | i <;> simp }
  have hinj : Function.Injective ι := by
    intro a b hab
    ext j
    have := congrArg
      (fun z : LinearMap.ker (Matrix.toLin' (blockAdj (k := k) A)) =>
        (z : Fin m ⊕ Fin k → ℝ) (Sum.inr j)) hab
    simpa [ι] using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  omega

end ZeroModes

/-! ## Berger spheres under Ricci flow (`x = a²`, `z = c²`) -/

section Berger

noncomputable def r1 (x z : ℝ) : ℝ := 2 * (2 * x - z) / x ^ 2
noncomputable def r3 (x z : ℝ) : ℝ := 2 * z / x ^ 2

theorem scalar_curv (x z : ℝ) (hx : x ≠ 0) : 2 * r1 x z + r3 x z = 8 / x - 2 * z / x ^ 2 := by
  unfold r1 r3; field_simp; ring

theorem ric_sq (x z : ℝ) (hx : x ≠ 0) :
    2 * r1 x z ^ 2 + r3 x z ^ 2 = 4 * (2 * (2 * x - z) ^ 2 + z ^ 2) / x ^ 4 := by
  unfold r1 r3; field_simp; ring

/-- `|Rm|² = 4|Ric|² − R²` in dimension three reproduces the paper's formula. -/
theorem rm_sq (x z : ℝ) (hx : x ≠ 0) :
    4 * (2 * r1 x z ^ 2 + r3 x z ^ 2) - (2 * r1 x z + r3 x z) ^ 2
      = 4 * (16 * x ^ 2 - 24 * x * z + 11 * z ^ 2) / x ^ 4 := by
  unfold r1 r3; field_simp; ring

theorem rm_sq_fibre_collapse (x : ℝ) (hx : x ≠ 0) :
    4 * (16 * x ^ 2 - 24 * x * 0 + 11 * 0 ^ 2) / x ^ 4 = 64 / x ^ 2 := by
  field_simp; ring

/-- Ratio equation: from `ẋ = −2 r₁ x`, `ż = −2 r₃ z` one gets `u̇ = 8u(1−u)/x`, `u = z/x`. -/
theorem ratio_ode {X Z : ℝ → ℝ} {t : ℝ} (hx : X t ≠ 0)
    (hX : HasDerivAt X (-2 * r1 (X t) (Z t) * X t) t)
    (hZ : HasDerivAt Z (-2 * r3 (X t) (Z t) * Z t) t) :
    HasDerivAt (fun s => Z s / X s)
      (8 * (Z t / X t) * (1 - Z t / X t) / X t) t := by
  convert hZ.div hX hx using 1
  unfold r1 r3; field_simp; ring

end Berger

/-! ## GHZ branch balancing -/

section GHZ

variable {c s A B g : ℝ}

theorem design_factorization (hc : 0 < c) (hs : 0 < s) (hA : 0 < A) (hB : 0 < B) :
    let q := g / √(A * B)
    let r := c * √A / (s * √B)
    2 * c * s * g / (c ^ 2 * A + s ^ 2 * B) = q * (2 * r / (1 + r ^ 2)) ∧
      2 * r / (1 + r ^ 2) = 1 / Real.cosh (Real.log r) := by
  intro q r
  have hA' : 0 < √A := Real.sqrt_pos.mpr hA
  have hB' : 0 < √B := Real.sqrt_pos.mpr hB
  have hAA : √A ^ 2 = A := Real.sq_sqrt hA.le
  have hBB : √B ^ 2 = B := Real.sq_sqrt hB.le
  have hr : 0 < r := by positivity
  constructor
  · simp only [q, r]
    rw [Real.sqrt_mul hA.le]
    field_simp
    rw [hAA, hBB]; ring
  · rw [Real.cosh_log hr]; field_simp; ring

/-- `2r/(1+r²) ≤ 1` with equality iff `r = 1`, hence `V ≤ q` (`= q` iff branch balance). -/
theorem balance_penalty (r : ℝ) (hr : 0 < r) :
    2 * r / (1 + r ^ 2) ≤ 1 ∧ (2 * r / (1 + r ^ 2) = 1 ↔ r = 1) := by
  have h : 0 < 1 + r ^ 2 := by positivity
  constructor
  · rw [div_le_one h]; nlinarith [sq_nonneg (r - 1)]
  · rw [div_eq_one_iff_eq h.ne']
    constructor
    · intro e; nlinarith [sq_nonneg (r - 1)]
    · rintro rfl; norm_num

end GHZ

/-! ## Dilation algebra of round valuation profiles -/

section Dilation

/-- **Homogeneous work identity**: with `E = ε·V`, `V = 2π²A³` and `dE = −p dV`,
`p = −ε − (A/3) ε'`. -/
theorem work_identity {ε : ℝ → ℝ} {ε' A : ℝ} (hA : A ≠ 0) (hε : HasDerivAt ε ε' A) :
    HasDerivAt (fun a => ε a * (2 * π ^ 2 * a ^ 3))
      (ε' * (2 * π ^ 2 * A ^ 3) + ε A * (6 * π ^ 2 * A ^ 2)) A ∧
    -(ε' * (2 * π ^ 2 * A ^ 3) + ε A * (6 * π ^ 2 * A ^ 2)) / (6 * π ^ 2 * A ^ 2)
      = -ε A - A / 3 * ε' := by
  constructor
  · have hV : HasDerivAt (fun a : ℝ => 2 * π ^ 2 * a ^ 3) (6 * π ^ 2 * A ^ 2) A := by
      have := (hasDerivAt_pow 3 A).const_mul (2 * π ^ 2)
      convert this using 1; push_cast; ring
    exact hε.mul hV
  · have : π ≠ 0 := Real.pi_ne_zero
    field_simp; ring

/-- `D = A d/dA` acts on `A^n` (`n ∈ ℤ`, `A ≠ 0`) with eigenvalue `n`. -/
theorem dilation_eigen (n : ℤ) {A : ℝ} (hA : A ≠ 0) :
    A * deriv (fun t : ℝ => t ^ n) A = n * A ^ n := by
  rw [deriv_zpow, show A * (↑n * A ^ (n - 1)) = n * (A * A ^ (n - 1)) by ring,
    ← zpow_one_add₀ hA]
  congr 2; ring

/-- Integer roots of `P_val(z) = (z−1) z (z+1)(z+2)(z+3)`. -/
theorem P_val_roots (z : ℤ) :
    (z - 1) * z * (z + 1) * (z + 2) * (z + 3) = 0 ↔ z ∈ ({1, 0, -1, -2, -3} : Set ℤ) := by
  simp only [mul_eq_zero, sub_eq_zero, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- Round valuation density `ε = E_val/V₃` has exactly the exponents `1, 0, −1, −2, −3`. -/
theorem valuation_density (A γ α₀ α₁ α₂ α₃ : ℝ) (hA : A ≠ 0) :
    (π ^ 2 / 2 * γ * A ^ 4 + 2 * π ^ 2 * (α₀ * A ^ 3 + 3 * α₁ * A ^ 2 + 3 * α₂ * A + α₃))
        / (2 * π ^ 2 * A ^ 3)
      = γ / 4 * A + α₀ + 3 * α₁ * A⁻¹ + 3 * α₂ * A⁻¹ ^ 2 + α₃ * A⁻¹ ^ 3 := by
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp; ring

end Dilation

/-! ## Trace-free gravity -/

section TraceFree

open Matrix

/-- Trace-free projection with respect to an invertible 4×4 metric. -/
noncomputable def Ptr (g T : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  T - (1 / 4 * trace (g⁻¹ * T)) • g

/-- **Vacuum-energy kernel**: a constant vacuum shift `T ↦ T − ρ₀ g` is invisible. -/
theorem vacuum_kernel (g T : Matrix (Fin 4) (Fin 4) ℝ) (hg : IsUnit g.det) (ρ₀ : ℝ) :
    Ptr g (T - ρ₀ • g) = Ptr g T := by
  unfold Ptr
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.nonsing_inv_mul g hg, trace_sub, trace_smul,
    trace_one]
  simp only [Fintype.card_fin, smul_eq_mul]
  rw [show (1 / 4 : ℝ) * (trace (g⁻¹ * T) - ρ₀ * ((4 : ℕ) : ℝ)) = 1 / 4 * trace (g⁻¹ * T) - ρ₀ by
    push_cast; ring, sub_smul]
  abel

/-- de Sitter capacity map. -/
theorem de_sitter_capacity {ℓ q : ℝ} (hℓ : 0 < ℓ) (hq : 0 < q) :
    3 / (ℓ * √(q / π)) ^ 2 = 3 * π / (q * ℓ ^ 2) := by
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp

end TraceFree

end FBS3R.Checks
