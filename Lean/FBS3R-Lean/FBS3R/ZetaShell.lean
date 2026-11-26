/-
# The ζ-constants of the curl-shell barriers on `S³`

Source: *Killing–Beltrami algebra and exact reductions of Navier–Stokes flow on the
three-sphere*, Cor. `cor:globalfractional` and Prop. `prop:zetapole`.

Machine-checked here:
* (shell sum) for real `s > 3`,
  `Σ_{k ≥ 0} Σ_{σ = ±} (k+1)(k+3)/(k+2)^s = 2 (ζ(s-2) - ζ(s))`,
  where `ζ(s) = Σ_{n≥1} n^{-s}`; and this real `ζ` agrees with Mathlib's `riemannZeta`.
* (volume normalisation) with `V_R = 2π²R³`: `2R^s/(3V_R) = R^{s-3}/(3π²)`.
* (exact pole, Prop. `prop:zetapole`) `lim_{s↓3} (s-3) · C_s(R) = 1/(3π²)`,
  where `C_s(R) = R^{s-3}/(3π²) · (ζ(s-2) - ζ(s))`.
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace FBS3R.ZetaShell

open Real Filter Topology

/-- Real zeta function for `s > 1`: `Z s = Σ_{n ≥ 0} 1/(n+1)^s`. -/
noncomputable def Z (s : ℝ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s

lemma summable_Z {s : ℝ} (hs : 1 < s) : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  simpa using this

/-- `Z` agrees with Mathlib's Riemann zeta function on real `s > 1`. -/
theorem Z_eq_riemannZeta {s : ℝ} (hs : 1 < s) : (Z s : ℂ) = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs), Z, Complex.ofReal_tsum]
  congr 1; ext n
  push_cast
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

/-- Termwise identity `n^{2-s} - n^{-s} = (n²-1)/n^s` at `n = k+1`. -/
lemma term_id (s : ℝ) (n : ℕ) :
    1 / ((n : ℝ) + 1) ^ (s - 2) - 1 / ((n : ℝ) + 1) ^ s
      = (((n : ℝ) + 1) ^ 2 - 1) / ((n : ℝ) + 1) ^ s := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.rpow_sub hpos, Real.rpow_two]
  have h1 : (0 : ℝ) < ((n : ℝ) + 1) ^ s := Real.rpow_pos_of_pos hpos s
  field_simp

/-- **Shell sum** (Cor. `cor:globalfractional`):
`Σ_k 2·(k+1)(k+3)/(k+2)^s = 2(ζ(s-2) - ζ(s))` for `s > 3`. -/
theorem shell_sum {s : ℝ} (hs : 3 < s) :
    ∑' k : ℕ, 2 * (((k : ℝ) + 1) * ((k : ℝ) + 3) / ((k : ℝ) + 2) ^ s)
      = 2 * (Z (s - 2) - Z s) := by
  have hA := summable_Z (s := s - 2) (by linarith)
  have hB := summable_Z (s := s) (by linarith)
  rw [Z, Z, ← hA.tsum_sub hB]
  have hsum : Summable (fun n : ℕ =>
      1 / ((n : ℝ) + 1) ^ (s - 2) - 1 / ((n : ℝ) + 1) ^ s) := hA.sub hB
  rw [hsum.tsum_eq_zero_add, tsum_mul_left]
  simp only [term_id]
  congr 1
  simp only [Nat.cast_zero, zero_add, one_pow, sub_self, zero_div]
  congr 1; ext k
  push_cast
  rw [show ((k : ℝ) + 1 + 1) = k + 2 by ring]
  ring

/-- Volume normalisation: with `V_R = 2π²R³`, `2R^s/(3V_R) = R^{s-3}/(3π²)`. -/
theorem constant_normalisation {R : ℝ} (hR : 0 < R) (s : ℝ) :
    2 * R ^ s / (3 * (2 * π ^ 2 * R ^ 3)) = R ^ (s - 3) / (3 * π ^ 2) := by
  rw [Real.rpow_sub hR, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have : 0 < R ^ 3 := by positivity
  have : 0 < π := Real.pi_pos
  field_simp

/-- The embedding constant `C_s(R)` of Prop. `prop:zetapole`. -/
noncomputable def C (R s : ℝ) : ℝ := R ^ (s - 3) / (3 * π ^ 2) * (Z (s - 2) - Z s)

/-- Simple pole of the real zeta function: `(t - 1)·Z(t) → 1` as `t ↓ 1`. -/
theorem tendsto_sub_one_mul_Z : Tendsto (fun t => (t - 1) * Z t) (𝓝[>] 1) (𝓝 1) := by
  have key : ∀ t, 1 < t → (t - 1) * Z t = 1 + (t - 1) * (1 - t * ZetaAsymptotics.termTSum t) := by
    intro t ht
    have := ZetaAsymptotics.zeta_limit_aux1 ht
    have hZ : Z t = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ t := rfl
    rw [hZ, ← this]
    have : t - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hcont : ContinuousWithinAt (fun t => 1 - t * ZetaAsymptotics.termTSum t)
      (Set.Ioi 1) 1 := by
    have := ZetaAsymptotics.continuousOn_termTSum 1 (Set.mem_Ici.mpr le_rfl)
    exact ((continuousWithinAt_const.sub
      (continuousWithinAt_id.mul this)).mono Set.Ioi_subset_Ici_self)
  have hlim : Tendsto (fun t => 1 + (t - 1) * (1 - t * ZetaAsymptotics.termTSum t))
      (𝓝[>] 1) (𝓝 (1 + (1 - 1) * (1 - 1 * ZetaAsymptotics.termTSum 1))) := by
    apply tendsto_const_nhds.add
    apply Tendsto.mul
    · exact ((continuous_sub_right (1 : ℝ)).tendsto' 1 (1 - 1) rfl).mono_left
        nhdsWithin_le_nhds
    · exact hcont.tendsto
  simp only [sub_self, zero_mul, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (key t ht).symm

lemma Z_antitone_on {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : Z t ≤ Z s := by
  apply Summable.tsum_le_tsum _ (summable_Z (by linarith)) (summable_Z hs)
  intro n
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith) s)
  exact Real.rpow_le_rpow_of_exponent_le h1 hst

lemma Z_nonneg (s : ℝ) : 0 ≤ Z s := tsum_nonneg fun n => by positivity

/-- **Exact pole of the supercritical embedding constant** (Prop. `prop:zetapole`):
`lim_{s ↓ 3} (s - 3) C_s(R) = 1/(3π²)` for every radius `R > 0`. -/
theorem residue_C {R : ℝ} (hR : 0 < R) :
    Tendsto (fun s => (s - 3) * C R s) (𝓝[>] 3) (𝓝 (1 / (3 * π ^ 2))) := by
  -- (s-3) Z(s-2) → 1
  have h1 : Tendsto (fun s => (s - 3) * Z (s - 2)) (𝓝[>] 3) (𝓝 1) := by
    have hmap : Tendsto (fun s : ℝ => s - 2) (𝓝[>] 3) (𝓝[>] 1) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact ((continuous_sub_right (2 : ℝ)).tendsto' 3 1 (by norm_num)).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_Ioi] at hs ⊢; linarith
    have := tendsto_sub_one_mul_Z.comp hmap
    refine this.congr' (Eventually.of_forall fun s => ?_)
    simp only [Function.comp]; ring_nf
  -- (s-3) Z(s) → 0, squeezed by 0 ≤ (s-3) Z s ≤ (s-3) Z 3
  have h2 : Tendsto (fun s => (s - 3) * Z s) (𝓝[>] 3) (𝓝 0) := by
    have hup : Tendsto (fun s => (s - 3) * Z 3) (𝓝[>] 3) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ => (s - 3) * Z 3) := by fun_prop
      exact (hc.tendsto' 3 0 (by simp)).mono_left nhdsWithin_le_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_nonneg (by simp only [Set.mem_Ioi] at hs; linarith) (Z_nonneg s)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs
      exact mul_le_mul_of_nonneg_left (Z_antitone_on (by norm_num) hs.le) (by linarith)
  -- R^(s-3) → 1
  have h3 : Tendsto (fun s : ℝ => R ^ (s - 3) / (3 * π ^ 2)) (𝓝[>] 3)
      (𝓝 (1 / (3 * π ^ 2))) := by
    have hc : Continuous (fun s : ℝ => R ^ (s - 3) / (3 * π ^ 2)) := by
      apply Continuous.div_const
      exact (continuous_const.rpow (continuous_id.sub continuous_const)
        (fun _ => Or.inl hR.ne'))
    have := hc.tendsto 3
    simp only [sub_self, Real.rpow_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := h3.mul (h1.sub h2)
  simp only [sub_zero, mul_one] at this
  refine this.congr' (Eventually.of_forall fun s => ?_)
  simp only [C]; ring

end FBS3R.ZetaShell
