/-
# Conditional spectral-entropy lower bound

Source: *Killing–Beltrami algebra …*, Prop. `prop:conditionalentropy`:
if a set `S` of `M` shells carries total probability `q = Σ_{α∈S} p_α ≥ δ > 0` and
`p_α ≤ C/M` on `S`, then for `M ≥ C`: `S_spec ≥ δ log(M/C)`.

Fully machine-checked for an arbitrary finite probability vector (the shell energy
distribution); `Real.negMulLog x = -x log x`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace FBS3R.Entropy

open Real Finset

theorem conditional_entropy_bound {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (S : Finset ι) (C δ : ℝ)
    (hC : 0 < C) (hM : C ≤ S.card) (hδ : δ ≤ ∑ i ∈ S, p i)
    (hcap : ∀ i ∈ S, p i ≤ C / S.card) :
    δ * Real.log (S.card / C) ≤ ∑ i, Real.negMulLog (p i) := by
  have hcard : (0 : ℝ) < S.card := lt_of_lt_of_le hC hM
  have hle1 : ∀ i, p i ≤ 1 := fun i => by
    rw [← hp1]; exact single_le_sum (fun j _ => hp0 j) (mem_univ i)
  have hL : 0 ≤ Real.log (S.card / C) := Real.log_nonneg (by rw [le_div_iff₀ hC]; linarith)
  -- termwise: on S, negMulLog (p i) ≥ p i * log (M/C)
  have hterm : ∀ i ∈ S, p i * Real.log (S.card / C) ≤ Real.negMulLog (p i) := by
    intro i hi
    rcases (hp0 i).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [Real.negMulLog, neg_mul, ← mul_neg, ← Real.log_inv]
      apply mul_le_mul_of_nonneg_left _ h.le
      apply Real.log_le_log (div_pos hcard hC)
      rw [le_inv_comm₀ (div_pos hcard hC) h, inv_div]
      exact hcap i hi
  calc δ * Real.log (S.card / C) ≤ (∑ i ∈ S, p i) * Real.log (S.card / C) :=
        mul_le_mul_of_nonneg_right hδ hL
    _ = ∑ i ∈ S, p i * Real.log (S.card / C) := by rw [sum_mul]
    _ ≤ ∑ i ∈ S, Real.negMulLog (p i) := sum_le_sum hterm
    _ ≤ ∑ i, Real.negMulLog (p i) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ S)
          (fun i _ _ => Real.negMulLog_nonneg (hp0 i) (hle1 i))

end FBS3R.Entropy
