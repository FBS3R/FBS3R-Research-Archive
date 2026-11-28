/-
# The "uniqueness of the Fibonacci stratification" theorem is vacuous/false

Sources: *Compact Simply-Connected Cosmology and the Geometric Origin of Quantum
Nonlocality …* (2026-04-15), Thm `thm:unique-fib`, and *Geometric Infrared Scale of
Yang–Mills Theory on a Compact Three-Manifold …* (2026-04-19), Thm `thm:unique`.

Both state: among gapless partitions of `ℤ_{≥1}` into intervals `[a_n, a_{n+1})` with
`a_1 = 1`, strictly increasing boundaries, convergent ratio `a_{n+1}/a_n → r > 1` and
**additive closure** (`a_m + a_n = a_k` for some `k`), the Fibonacci partition is the
unique one (with `r = φ`).

Machine-checked here:
* the Fibonacci numbers are **not** additively closed (`F₂ + F₅ = 6` is not Fibonacci);
* stronger: **no** sequence satisfies the hypotheses at all — additive closure plus
  `a₀ = 1` and strict monotonicity force `a n = n + 1`, whose ratio tends to `1`, not to
  any `r > 1`.  So the "uniqueness" theorem has an empty hypothesis class.
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace FBS3R.FibStrat

open Filter Topology

theorem fib_not_additively_closed : ¬ ∀ m n : ℕ, ∃ k, Nat.fib m + Nat.fib n = Nat.fib k := by
  intro H
  obtain ⟨k, hk⟩ := H 2 5
  have h6 : Nat.fib k = 6 := by rw [← hk]; decide
  rcases Nat.lt_or_ge k 6 with h | h
  · have := Nat.fib_mono (Nat.le_of_lt_succ h)
    rw [h6] at this; exact absurd this (by decide)
  · have := Nat.fib_mono h
    rw [h6] at this; exact absurd this (by decide)

/-- Additive closure + `a 0 = 1` + strict monotonicity force `a n = n + 1`. -/
theorem forced_identity (a : ℕ → ℕ) (hmono : StrictMono a) (h0 : a 0 = 1)
    (hclos : ∀ m n, ∃ k, a m + a n = a k) : ∀ n, a n = n + 1 := by
  have lower : ∀ n, n + 1 ≤ a n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have := hmono (show n < n + 1 by omega); omega
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    obtain ⟨k, hk⟩ := hclos n 0
    rw [ih, h0] at hk
    have hkn : n < k := by
      by_contra hcon
      push_neg at hcon
      have := hmono.monotone hcon
      omega
    have := hmono.monotone (show n + 1 ≤ k by omega)
    have := lower (n + 1)
    omega

/-- **No partition satisfies the hypotheses of the "uniqueness" theorem.** -/
theorem no_additively_closed_partition_with_ratio_gt_one :
    ¬ ∃ (a : ℕ → ℕ) (r : ℝ), StrictMono a ∧ a 0 = 1 ∧ (∀ m n, ∃ k, a m + a n = a k) ∧
      1 < r ∧ Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 r) := by
  rintro ⟨a, r, hmono, h0, hclos, hr, hlim⟩
  have ha := forced_identity a hmono h0 hclos
  have hratio : Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) atTop (𝓝 1) := by
    have e : (fun n : ℕ => (a (n + 1) : ℝ) / a n) = fun n : ℕ => 1 + 1 / ((n : ℝ) + 1) := by
      funext n; rw [ha, ha]; push_cast
      have : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    rw [e]
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add this
  have := tendsto_nhds_unique hlim hratio
  linarith

end FBS3R.FibStrat

namespace FBS3R.FibStrat

open Filter Topology

/-! ### What is true: the Fibonacci partition and golden-ratio scaling

(2026-04-19, Thm `thm:partition` and Thm `thm:fibscaling`.) The intervals
`[F_n, F_{n+1})`, `n ≥ 2`, partition `ℤ_{≥1}`, and `F_{n+1}/F_n → φ`. -/

theorem fib_partition (m : ℕ) (hm : 1 ≤ m) :
    ∃! n, 2 ≤ n ∧ Nat.fib n ≤ m ∧ m < Nat.fib (n + 1) := by
  refine ⟨Nat.greatestFib m, ⟨?_, Nat.fib_greatestFib_le m, Nat.lt_fib_greatestFib_add_one m⟩, ?_⟩
  · exact Nat.le_greatestFib.mpr (by simpa using hm)
  · rintro n ⟨-, h1, h2⟩
    apply le_antisymm
    · exact Nat.le_greatestFib.mpr h1
    · exact Nat.lt_succ_iff.mp (Nat.greatestFib_lt.mpr h2)

theorem golden_scaling :
    Tendsto (fun n => (Nat.fib (n + 1) / Nat.fib n : ℝ)) atTop (𝓝 Real.goldenRatio) :=
  tendsto_fib_succ_div_fib_atTop

end FBS3R.FibStrat
