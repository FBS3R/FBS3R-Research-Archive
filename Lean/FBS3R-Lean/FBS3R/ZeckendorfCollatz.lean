/-
# Zeckendorf–φ height bounds for the Collatz map

Source: *Zeckendorf–φ Bounds for the Collatz Map: Strict Local Theory, Two Sufficient
Reductions and No-Go Results* (2025-09-28).

The paper defines the height `h(n)` as the largest index of the Zeckendorf representation
of `n` (with `F₁ = F₂ = 1`).  This is exactly Mathlib's `Nat.greatestFib n`
(the largest `k` with `fib k ≤ n`).

Machine-checked here:
* Lemma (even step), Lemma (odd step), Proposition (superstep drift `h(T n) - h n ≤ 3 - m`),
  for *every* `m` with `2^m ∣ 3n+1` (in particular `m = ν₂(3n+1)`).
* Proposition (naive Lyapunov `V = h - 2ν₂` fails): the paper's numbers are verified.
* Theorem (no coarse residue certificate): the self-loop at residue `1` has weight `+1`.
* **Counterexample** to Proposition "Refined odd-step": `n = 11` is *not* top-third
  (`{log_φ(√5·11)} < 2/3`) and yet `h(3·11+1) - h(11) = 3`.
-/
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace FBS3R.Collatz

open Nat

/-- Zeckendorf height `h(n)`: the largest `k` with `F_k ≤ n`. -/
abbrev h (n : ℕ) : ℕ := Nat.greatestFib n

/-- Characterisation used everywhere: `h n = k` iff `F_k ≤ n < F_{k+1}`. -/
lemma h_eq_iff {n k : ℕ} : h n = k ↔ fib k ≤ n ∧ n < fib (k + 1) := by
  constructor
  · rintro rfl; exact ⟨fib_greatestFib_le n, lt_fib_greatestFib_add_one n⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp (greatestFib_lt.mpr h2)
    · exact le_greatestFib.mpr h1

lemma fib_succ_le_two_mul (k : ℕ) (hk : 1 ≤ k) : fib (k + 1) ≤ 2 * fib k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := fib_add_two (n := j)
  have := fib_le_fib_succ (n := j)
  simp only [show j + 1 + 1 = j + 2 by ring] at *
  omega

/-- **Even step** (Lemma `lem:even`): `h(n/2) ≤ h(n) - 1`, i.e. `h(n/2) + 1 ≤ h(n)`, for `n ≥ 1`.
(The paper assumes `n` even; the bound holds for all `n ≥ 1` with floor division.) -/
theorem even_step {n : ℕ} (hn : 1 ≤ n) : h (n / 2) + 1 ≤ h n := by
  have hk : 1 ≤ h n := greatestFib_pos.mpr hn
  have h2 : n < fib (h n + 1) := lt_fib_greatestFib_add_one n
  have h3 := fib_succ_le_two_mul (h n) hk
  have : n / 2 < fib (h n) := by omega
  exact greatestFib_lt.mpr this

/-- **Odd step** (Lemma `lem:odd`): `h(3n+1) ≤ h(n) + 3` (valid for every `n`). -/
theorem odd_step (n : ℕ) : h (3 * n + 1) ≤ h n + 3 := by
  have h2 : n < fib (h n + 1) := lt_fib_greatestFib_add_one n
  set k := h n
  have e1 : fib (k + 4) = fib (k + 2) + fib (k + 3) := fib_add_two
  have e2 : fib (k + 3) = fib (k + 1) + fib (k + 2) := fib_add_two
  have e3 : fib (k + 2) = fib k + fib (k + 1) := fib_add_two
  have : 3 * n + 1 < fib (k + 4) := by omega
  exact Nat.lt_succ_iff.mp (greatestFib_lt.mpr this)

/-- Iterated halving: if `2^j ∣ x` and `x ≥ 1` then `h(x / 2^j) + j ≤ h(x)`. -/
theorem halving_iter : ∀ (j x : ℕ), 1 ≤ x → 2 ^ j ∣ x → h (x / 2 ^ j) + j ≤ h x
  | 0, x, _, _ => by simp
  | j + 1, x, hx, hd => by
    have hd' : 2 ^ j ∣ x := (pow_dvd_pow 2 (Nat.le_succ j)).trans hd
    have ih := halving_iter j x hx hd'
    have hpos : 1 ≤ x / 2 ^ j :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hd') (by positivity)
    have := even_step hpos
    rw [Nat.div_div_eq_div_mul, ← pow_succ] at this
    omega

/-- **Superstep drift** (Proposition `prop:super`): for `T(n) = (3n+1)/2^m` with `2^m ∣ 3n+1`,
`h(T n) - h(n) ≤ 3 - m`, stated without subtraction as `h(T n) + m ≤ h(n) + 3`. -/
theorem superstep_drift (n m : ℕ) (hm : 2 ^ m ∣ 3 * n + 1) :
    h ((3 * n + 1) / 2 ^ m) + m ≤ h n + 3 :=
  (halving_iter m (3 * n + 1) (by omega) hm).trans (odd_step n)

/-- Same statement in `ℤ`, literally `h(T(n)) - h(n) ≤ 3 - m`. -/
theorem superstep_drift_int (n m : ℕ) (hm : 2 ^ m ∣ 3 * n + 1) :
    (h ((3 * n + 1) / 2 ^ m) : ℤ) - h n ≤ 3 - m := by
  have := superstep_drift n m hm; omega

/-! ### Concrete values (all checked by the kernel, no `native_decide`). -/

lemma h_one : h 1 = 2 := h_eq_iff.mpr ⟨by decide, by decide⟩
lemma h_three : h 3 = 4 := h_eq_iff.mpr ⟨by decide, by decide⟩
lemma h_five : h 5 = 5 := h_eq_iff.mpr ⟨by decide, by decide⟩
lemma h_ten : h 10 = 6 := h_eq_iff.mpr ⟨by decide, by decide⟩
lemma h_eleven : h 11 = 6 := h_eq_iff.mpr ⟨by decide, by decide⟩
lemma h_34 : h 34 = 9 := h_eq_iff.mpr ⟨by decide, by decide⟩

/-- Proposition `prop:noV`: `V(n) = h(n) - 2ν₂(n)` increases on `10 ↦ 5` and on `3 ↦ 5`
(ν₂(10) = 1, ν₂(5) = ν₂(3) = 0). Values `V(10)=4, V(5)=5, V(3)=4` as in the paper. -/
theorem naive_lyapunov_fails :
    ((h 10 : ℤ) - 2 * 1 = 4) ∧ ((h 5 : ℤ) - 2 * 0 = 5) ∧ ((h 3 : ℤ) - 2 * 0 = 4) := by
  simp [h_ten, h_five, h_three]

/-- Theorem `thm:nocoarse`: the residue `1` maps to itself (`(3·1+1)/2² = 1`) with weight
`3 - 2 = 1 > 0`, so no potential `ξ` with `ξ(r') - ξ(r) + w(r) ≤ -ε`, `ε > 0`, exists. -/
theorem no_coarse_certificate (ξ : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ¬ (ξ ((3 * 1 + 1) / 2 ^ 2) - ξ 1 + (3 - 2 : ℝ) ≤ -ε) := by
  norm_num; linarith

/-! ### Counterexample to Proposition `prop:topthird` ("Refined odd-step")

The paper: with `x(n) = log_φ(√5 · n)`, call `n` *top-third* if `{x(n)} ∈ [2/3, 1)`;
"if `n` is top-third then `h(3n+1) - h(n) ≤ 3`; **otherwise the increase is `≤ 2`**".
For `n = 11`: `x(11) ∈ [6, 6 + 2/3)`, so `11` is not top-third, but the increase is `3`.
(An exhaustive search over odd `n ≤ 2·10⁶` finds `n = 11` as the only violation, so the
claim is “asymptotically” plausible but false as stated.) -/

open Real

/-- `Real.goldenRatio^6 < √5·11`, i.e. `x(11) > 6`. -/
lemma phi_pow_six_lt : Real.goldenRatio ^ 6 < √5 * 11 := by
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √5 := by positivity
  have : Real.goldenRatio ^ 6 = 8 * Real.goldenRatio + 5 := by
    have := goldenRatio_mul_fib_succ_add_fib 5
    norm_num [Nat.fib_add_two] at this ⊢; linarith
  rw [this]; simp only [Real.goldenRatio]; nlinarith

/-- `(√5·11)^3 < Real.goldenRatio^20`, i.e. `x(11) < 6 + 2/3`. -/
lemma cube_lt_phi_pow_twenty : (√5 * 11) ^ 3 < Real.goldenRatio ^ 20 := by
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √5 := by positivity
  have : Real.goldenRatio ^ 20 = 6765 * Real.goldenRatio + 4181 := by
    have := goldenRatio_mul_fib_succ_add_fib 19
    norm_num [Nat.fib_add_two] at this ⊢; linarith
  rw [this]; simp only [Real.goldenRatio]
  have hs : √5 < 2.25 := by nlinarith
  nlinarith

theorem refined_odd_step_counterexample :
    let x := Real.logb Real.goldenRatio (√5 * 11)
    6 ≤ x ∧ x < 6 + 2 / 3 ∧ h (3 * 11 + 1) = h 11 + 3 := by
  intro x
  have hReal.goldenRatio : 1 < Real.goldenRatio := one_lt_goldenRatio
  have hpos : 0 < √5 * 11 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have := phi_pow_six_lt
    rw [Real.le_logb_iff_rpow_le hReal.goldenRatio hpos]
    exact_mod_cast this.le
  · rw [Real.logb_lt_iff_lt_rpow hReal.goldenRatio hpos]
    have h3 := cube_lt_phi_pow_twenty
    have : Real.goldenRatio ^ (6 + 2 / 3 : ℝ) = (Real.goldenRatio ^ (20 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_mul goldenRatio_pos.le]; norm_num
    rw [this]
    have hc : √5 * 11 = ((√5 * 11) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_mul hpos.le]; norm_num
    rw [hc]
    apply Real.rpow_lt_rpow (by positivity) _ (by norm_num)
    exact_mod_cast h3
  · show h 34 = h 11 + 3
    rw [h_34, h_eleven]

end FBS3R.Collatz
