/-
# Small checks from the archive

* Mandelbrot preprint (2025-03-05), the step on source line 213: "`U ⊆` a connected disc,
  hence `U` is connected".  False in general: `{0, 1} ⊆ [0, 1]`.
* Killing–Beltrami, Prop. `prop:singleslope`: the cancellation slope `c*(k) = k/(k+4)` is
  injective, so one graph subalgebra cannot serve two levels.
* Killing–Beltrami, Prop. `prop:helicitydissipation`: on a single shell
  `⟨A v, curl v⟩ = κ_k · σ(k+2)/R · ‖v‖²`, sign-indefinite in `σ`.
-/
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace FBS3R.Misc

/-- A subset of a connected set need not be connected. -/
theorem subset_of_connected_not_connected :
    ∃ S T : Set ℝ, IsConnected T ∧ S ⊆ T ∧ S.Nonempty ∧ ¬ IsPreconnected S := by
  refine ⟨{0, 1}, Set.Icc 0 1, isConnected_Icc (by norm_num), ?_, ⟨0, by simp⟩, ?_⟩
  · intro x hx; rcases hx with rfl | rfl <;> simp
  · intro h
    have := h.Icc_subset (a := 0) (b := 1) (by simp) (by simp)
    have h2 : (1 / 2 : ℝ) ∈ ({0, 1} : Set ℝ) := this ⟨by norm_num, by norm_num⟩
    rcases h2 with h2 | h2 <;> norm_num at h2

/-- The single-slope map `k ↦ k/(k+4)` is injective. -/
theorem single_slope_injective {k₁ k₂ : ℕ} (h : (k₁ : ℝ) / (k₁ + 4) = k₂ / (k₂ + 4)) :
    k₁ = k₂ := by
  have h1 : (k₁ : ℝ) + 4 ≠ 0 := by positivity
  have h2 : (k₂ : ℝ) + 4 ≠ 0 := by positivity
  field_simp at h
  exact_mod_cast (by linarith : (k₁ : ℝ) = k₂)

/-- Helicity dissipation on one shell flips sign with chirality. -/
theorem helicity_sign (κ R n : ℝ) (k : ℕ) (hκ : 0 < κ) (hR : 0 < R) (hn : 0 < n) :
    0 < κ * (1 * (k + 2) / R) * n ∧ κ * ((-1) * (k + 2) / R) * n < 0 := by
  have : (0 : ℝ) < k + 2 := by positivity
  constructor
  · positivity
  · have : 0 < κ * ((k + 2) / R) * n := by positivity
    rw [show κ * ((-1) * (k + 2) / R) * n = -(κ * ((k + 2) / R) * n) by ring]
    linarith
end FBS3R.Misc
