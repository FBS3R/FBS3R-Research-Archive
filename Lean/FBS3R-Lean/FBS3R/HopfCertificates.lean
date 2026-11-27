/-
# Certified Hopf tomography and kernel coherence (2026-10-23, 2026-05-07)

Sources: *Certified Hopf Tomography: Exact Invariants, Sharp Stability and Minimax
Calibration* (2026-10-23) and *Multibranch kernels* (2026-05-07).

Machine-checked here:
* `mrw_norm_identity` : for the Moore–Ran–Wen vector
  `u = (sin kx, sin ky, sin kz, cos kx + cos ky + cos kz − m)`,
  `‖u‖² = 3 − Σ cᵢ² + (Σ cᵢ − m)²` with `cᵢ = cos kᵢ`;
* `mrw_gap_lower` / `mrw_gap_attained` : on `[−1,1]³` that expression is
  `≥ min_{s∈{−3,−1,1,3}} (s − m)²` (multi-affine ⇒ vertex minimum), and the value
  `(s − m)²` is attained at a vertex — the paper's Proposition "Exact global gap";
* `bloch_norm` : `|z† σ z| = |z|²` for `z ∈ ℂ²`
  (`4|āb|² + (|a|² − |b|²)² = (|a|² + |b|²)²`), the step `‖h₀‖ = ‖u‖²`;
* `gap_homotopy` : `‖b − b₀‖ ≤ E` and `‖b₀‖ ≥ g₀` give `‖(1−t)b₀ + t b‖ ≥ g₀ − E` for
  `t ∈ [0,1]` (non-closing gap along the linear homotopy);
* `normalization_identity` : `‖b − c‖² = (‖b‖ − ‖c‖)² + ‖b‖‖c‖‖b̂ − ĉ‖²`;
* `pair_coherence` : a positive semidefinite 2×2 block has `K₁₂² ≤ K₁₁K₂₂`;
* `filtering_invariance` : the normalised coherence `K_ij²/(K_iiK_jj)` is unchanged by
  diagonal positive filtering `K ↦ DKD`;
* `cycle_phase_gauge` : for unimodular `uᵢ`, the 3-cycle product `K₁₂K₂₃K₃₁` is invariant
  under the gauge `K_ij ↦ uᵢ K_ij ūⱼ`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace FBS3R.HopfCert

open Real

/-- The MRW norm identity. -/
theorem mrw_norm_identity (kx ky kz m : ℝ) :
    sin kx ^ 2 + sin ky ^ 2 + sin kz ^ 2 + (cos kx + cos ky + cos kz - m) ^ 2
      = 3 - (cos kx ^ 2 + cos ky ^ 2 + cos kz ^ 2) + (cos kx + cos ky + cos kz - m) ^ 2 := by
  have := sin_sq_add_cos_sq kx; have := sin_sq_add_cos_sq ky; have := sin_sq_add_cos_sq kz
  linarith

/-- The MRW gap function. -/
def f (m x y z : ℝ) : ℝ := 3 - (x ^ 2 + y ^ 2 + z ^ 2) + (x + y + z - m) ^ 2

/-- An affine function of `t ∈ [−1,1]` is at least its smaller endpoint value. -/
lemma affine_ge_min (α β t : ℝ) (ht : -1 ≤ t ∧ t ≤ 1) :
    min (α - β) (α + β) ≤ α + β * t := by
  rcases le_total 0 β with h | h
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

/-- `f` is affine in each variable. -/
lemma f_affine_x (m x y z : ℝ) :
    f m x y z = (3 + m ^ 2 + 2 * y * z - 2 * m * (y + z)) + (2 * (y + z) - 2 * m) * x := by
  unfold f; ring

lemma f_affine_y (m x y z : ℝ) :
    f m x y z = (3 + m ^ 2 + 2 * x * z - 2 * m * (x + z)) + (2 * (x + z) - 2 * m) * y := by
  unfold f; ring

lemma f_affine_z (m x y z : ℝ) :
    f m x y z = (3 + m ^ 2 + 2 * x * y - 2 * m * (x + y)) + (2 * (x + y) - 2 * m) * z := by
  unfold f; ring

lemma f_vertex (m x y z : ℝ) (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hz : z = 1 ∨ z = -1) : ∃ s ∈ ({-3, -1, 1, 3} : Set ℝ), f m x y z = (s - m) ^ 2 := by
  refine ⟨x + y + z, ?_, ?_⟩
  · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
      norm_num
  · unfold f
    have h1 : x ^ 2 = 1 := by rcases hx with rfl | rfl <;> norm_num
    have h2 : y ^ 2 = 1 := by rcases hy with rfl | rfl <;> norm_num
    have h3 : z ^ 2 = 1 := by rcases hz with rfl | rfl <;> norm_num
    rw [h1, h2, h3]; ring

/-- **Exact MRW gap, lower bound**: on the cube the gap function is at least the value
`(s − m)²` at some `s ∈ {−3,−1,1,3}`. -/
theorem mrw_gap_lower (m x y z : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1)
    (hz : -1 ≤ z ∧ z ≤ 1) :
    ∃ s ∈ ({-3, -1, 1, 3} : Set ℝ), (s - m) ^ 2 ≤ f m x y z := by
  -- reduce `x` to a vertex
  have step : ∀ (g : ℝ → ℝ) (t : ℝ), (-1 ≤ t ∧ t ≤ 1) → (∃ α β, ∀ u, g u = α + β * u) →
      ∃ v, (v = 1 ∨ v = -1) ∧ g v ≤ g t := by
    intro g t ht ⟨α, β, hg⟩
    have := affine_ge_min α β t ht
    rcases min_choice (α - β) (α + β) with h | h
    · refine ⟨-1, Or.inr rfl, ?_⟩; rw [hg, hg t]; rw [h] at this; linarith
    · refine ⟨1, Or.inl rfl, ?_⟩; rw [hg, hg t]; rw [h] at this; linarith
  obtain ⟨x', hx', h1⟩ := step (fun u => f m u y z) x hx ⟨_, _, fun u => f_affine_x m u y z⟩
  obtain ⟨y', hy', h2⟩ := step (fun u => f m x' u z) y hy ⟨_, _, fun u => f_affine_y m x' u z⟩
  obtain ⟨z', hz', h3⟩ := step (fun u => f m x' y' u) z hz ⟨_, _, fun u => f_affine_z m x' y' u⟩
  obtain ⟨s, hs, he⟩ := f_vertex m x' y' z' hx' hy' hz'
  exact ⟨s, hs, by linarith⟩

/-- **Exact MRW gap, attainment**: each `(s − m)²`, `s ∈ {−3,−1,1,3}`, is a vertex value. -/
theorem mrw_gap_attained (m s : ℝ) (hs : s ∈ ({-3, -1, 1, 3} : Set ℝ)) :
    ∃ x y z : ℝ, (x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1) ∧ (z = 1 ∨ z = -1) ∧
      f m x y z = (s - m) ^ 2 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨-1, -1, -1, by norm_num, by norm_num, by norm_num, by unfold f; ring⟩
  · exact ⟨-1, -1, 1, by norm_num, by norm_num, by norm_num, by unfold f; ring⟩
  · exact ⟨-1, 1, 1, by norm_num, by norm_num, by norm_num, by unfold f; ring⟩
  · exact ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, by unfold f; ring⟩

/-- **Bloch-vector norm**: `|z†σz|² = |z|⁴` for `z = (a, b) ∈ ℂ²`. -/
theorem bloch_norm (a b : ℂ) :
    4 * Complex.normSq (starRingEnd ℂ a * b) + (Complex.normSq a - Complex.normSq b) ^ 2
      = (Complex.normSq a + Complex.normSq b) ^ 2 := by
  rw [Complex.normSq_mul, Complex.normSq_conj]; ring

section Normed
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Non-closing gap along the linear homotopy.** -/
theorem gap_homotopy (b b₀ : F) (g₀ E t : ℝ) (hb₀ : g₀ ≤ ‖b₀‖) (hE : ‖b - b₀‖ ≤ E)
    (ht : 0 ≤ t ∧ t ≤ 1) : g₀ - E ≤ ‖(1 - t) • b₀ + t • b‖ := by
  have h : (1 - t) • b₀ + t • b = b₀ + t • (b - b₀) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [h]
  have h1 : ‖t • (b - b₀)‖ ≤ E := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    calc t * ‖b - b₀‖ ≤ 1 * ‖b - b₀‖ := by gcongr; exact ht.2
      _ ≤ E := by linarith
  have h2 := norm_sub_norm_le b₀ (-(t • (b - b₀)))
  rw [sub_neg_eq_add, norm_neg] at h2
  linarith

/-- **Normalisation identity** `‖b−c‖² = (‖b‖−‖c‖)² + ‖b‖‖c‖‖b̂−ĉ‖²`. -/
theorem normalization_identity (b c : F) (hb : b ≠ 0) (hc : c ≠ 0) :
    ‖b - c‖ ^ 2 = (‖b‖ - ‖c‖) ^ 2
      + ‖b‖ * ‖c‖ * ‖(‖b‖⁻¹) • b - (‖c‖⁻¹) • c‖ ^ 2 := by
  have nb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have nc : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left,
    inner_smul_right]
  simp only [norm_inv, norm_norm, conj_trivial]
  field_simp
  ring

end Normed

/-- **Pair coherence**: if `a²p + 2abr + b²q ≥ 0` for all real `a, b` then `r² ≤ pq`. -/
theorem pair_coherence (p q r : ℝ) (h : ∀ a b : ℝ, 0 ≤ a ^ 2 * p + 2 * a * b * r + b ^ 2 * q) :
    r ^ 2 ≤ p * q := by
  have hp : 0 ≤ p := by simpa using h 1 0
  have hq : 0 ≤ q := by simpa using h 0 1
  rcases hp.lt_or_eq with hp | hp
  · have := h r (-p)
    nlinarith
  · subst hp
    by_contra hr
    have hr0 : r ≠ 0 := by intro h0; apply hr; rw [h0]; simp
    have := h (-(q + 1)) r
    have hr2 : 0 < r ^ 2 := by positivity
    nlinarith

/-- **Filtering invariance** of normalised coherence under `K ↦ DKD`, `D > 0` diagonal. -/
theorem filtering_invariance (Kij Kii Kjj di dj : ℝ) (hi : 0 < di) (hj : 0 < dj)
    (hKi : Kii ≠ 0) (hKj : Kjj ≠ 0) :
    (di * Kij * dj) ^ 2 / ((di * Kii * di) * (dj * Kjj * dj)) = Kij ^ 2 / (Kii * Kjj) := by
  field_simp

/-- **Cycle-phase gauge invariance** of the three-cycle product. -/
theorem cycle_phase_gauge (K12 K23 K31 u1 u2 u3 : ℂ) (h1 : Complex.normSq u1 = 1)
    (h2 : Complex.normSq u2 = 1) (h3 : Complex.normSq u3 = 1) :
    (u1 * K12 * starRingEnd ℂ u2) * (u2 * K23 * starRingEnd ℂ u3)
      * (u3 * K31 * starRingEnd ℂ u1) = K12 * K23 * K31 := by
  have e : ∀ u : ℂ, Complex.normSq u = 1 → u * starRingEnd ℂ u = 1 := by
    intro u hu; rw [Complex.mul_conj, hu]; simp
  have := e u1 h1; have := e u2 h2; have := e u3 h3
  linear_combination
    (K12 * K23 * K31 * u1 * starRingEnd ℂ u1 * u2 * starRingEnd ℂ u2) * (e u3 h3)
    + (K12 * K23 * K31 * u1 * starRingEnd ℂ u1) * (e u2 h2)
    + (K12 * K23 * K31) * (e u1 h1)

end FBS3R.HopfCert
