/-
# Capacity selectors, ring geometry and scalarisation
(2026-08-17, 2026-04-24, 2026-07-06, 2026-04-29, 2026-10-17)

Machine-checked here:
* `unique_selector` (2026-08-17, *Unique-selector theorem*): if the adjacent log-ratio
  `ρ_q = g(q+1) − g(q)` (`g = log Z`) is strictly decreasing on `ℤ` and
  `ρ_{q*−1} > 0 > ρ_{q*}`, then `q*` is the unique maximiser of `g`;
* `bounded_growth` (2026-08-17, no-go): `I_{q+1}/I_q ≤ C` gives
  `Z_{q+1}/Z_q ≤ C/(q+1) < 1` once `q + 1 > C` (with `Z_q = I_q/q!`);
* `chord_law` (2026-04-24/07-06): the chord of a circle of radius `R` over the
  central angle `2θ` has squared length `(2R sin θ)²`; `ring_spacing`: adjacent vertices
  of a regular `n`-gon are `2R sin(π/n)` apart;
* `sagitta_formula`, `sagitta_bounds`: `s = R − √(R² − L²/4) = (L²/4)/(R + √(R²−L²/4))`
  and `L²/(8R) ≤ s ≤ L²/(4R)` for `0 ≤ L ≤ 2R`;
* `fibonacci_minimal` (2026-04-29): for `p, q ≥ 1` the growth root
  `(p + √(p² + 4q))/2` of `x² = px + q` is `≥ φ`, with equality iff `p = q = 1`;
* `scalarisation` (2026-10-17): `B(s) = b̄ + e^{−γs}(B₀ − b̄)` solves
  `B' = −γ(B − b̄)` and `‖B(s) − b̄‖ = e^{−γs}‖B₀ − b̄‖` in any normed space.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace FBS3R.Selector

open Real

/-- **Unique-selector theorem.** -/
theorem unique_selector (g : ℤ → ℝ) (q₀ : ℤ)
    (hdec : StrictAnti fun q => g (q + 1) - g q)
    (hpos : 0 < g q₀ - g (q₀ - 1)) (hneg : g (q₀ + 1) - g q₀ < 0) :
    ∀ q, q ≠ q₀ → g q < g q₀ := by
  -- below: all ρ_q > 0 for q < q₀;  above: all ρ_q < 0 for q ≥ q₀
  have hbelow : ∀ q, q < q₀ → 0 < g (q + 1) - g q := by
    intro q hq
    have h1 : g (q₀ - 1 + 1) - g (q₀ - 1) ≤ g (q + 1) - g q :=
      hdec.antitone (by omega)
    simp only [sub_add_cancel] at h1; linarith
  have habove : ∀ q, q₀ ≤ q → g (q + 1) - g q < 0 := by
    intro q hq
    have h1 : g (q + 1) - g q ≤ g (q₀ + 1) - g q₀ := hdec.antitone hq
    linarith
  -- increasing up to q₀
  have up : ∀ n : ℕ, g (q₀ - (n + 1)) < g q₀ := by
    intro n
    induction n with
    | zero => simpa using hpos
    | succ k ih =>
      have := hbelow (q₀ - (k + 1 + 1)) (by omega)
      have e : q₀ - ((k : ℤ) + 1 + 1) + 1 = q₀ - (k + 1) := by ring
      rw [e] at this
      push_cast; linarith
  have down : ∀ n : ℕ, g (q₀ + (n + 1)) < g q₀ := by
    intro n
    induction n with
    | zero => simpa using hneg
    | succ k ih =>
      have := habove (q₀ + (k + 1)) (by omega)
      have e : q₀ + (↑k + 1) + 1 = q₀ + (↑(k + 1) + 1) := by push_cast; ring
      rw [e] at this
      linarith
  intro q hq
  rcases lt_or_gt_of_ne hq with h | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, q = q₀ - (n + 1) := ⟨(q₀ - q - 1).toNat, by omega⟩
    rw [hn]; exact up n
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, q = q₀ + (n + 1) := ⟨(q - q₀ - 1).toNat, by omega⟩
    rw [hn]; exact down n

/-- **Bounded-growth obstruction.** -/
theorem bounded_growth (I : ℕ → ℝ) (hI : ∀ q, 0 < I q) (C : ℝ) (q : ℕ)
    (hC : I (q + 1) / I q ≤ C) (hq : C < q + 1) :
    (I (q + 1) / (q + 1).factorial) / (I q / q.factorial) ≤ C / (q + 1) ∧ C / (q + 1) < 1 := by
  have hf : ((q + 1).factorial : ℝ) = (q + 1) * q.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have hq0 : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hIq := hI q
  have hq1 : (0 : ℝ) < q + 1 := by positivity
  constructor
  · rw [hf]
    have : (I (q + 1) / ((q + 1) * q.factorial)) / (I q / q.factorial)
        = (I (q + 1) / I q) / (q + 1) := by field_simp
    rw [this]; exact div_le_div_of_nonneg_right hC hq1.le
  · rw [div_lt_one hq1]; exact hq

/-- **Chord law.** -/
theorem chord_law (R θ : ℝ) :
    (R - R * cos (2 * θ)) ^ 2 + (R * sin (2 * θ)) ^ 2 = (2 * R * sin θ) ^ 2 := by
  rw [cos_two_mul, sin_two_mul]
  linear_combination (-4 * R ^ 2 * (1 - cos θ ^ 2)) * sin_sq_add_cos_sq θ

/-- **Ring spacing**: adjacent vertices of a regular `n`-gon of circumradius `R`. -/
theorem ring_spacing (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (hn : 1 ≤ n) :
    √((R - R * cos (2 * π / n)) ^ 2 + (R * sin (2 * π / n)) ^ 2) = 2 * R * sin (π / n) := by
  have e : 2 * π / n = 2 * (π / n) := by ring
  rw [e, chord_law]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ π / n := by positivity
  have h1 : π / n ≤ π := div_le_self pi_pos.le hn'
  exact sqrt_sq (mul_nonneg (by positivity) (sin_nonneg_of_nonneg_of_le_pi h0 h1))

/-- **Sagitta formula.** -/
theorem sagitta_formula (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L) (hLR : L ≤ 2 * R) :
    R - √(R ^ 2 - L ^ 2 / 4) = (L ^ 2 / 4) / (R + √(R ^ 2 - L ^ 2 / 4)) := by
  have hnn : 0 ≤ R ^ 2 - L ^ 2 / 4 := by nlinarith
  have hq := sq_sqrt hnn
  have hpos : 0 < R + √(R ^ 2 - L ^ 2 / 4) := by positivity
  rw [eq_div_iff hpos.ne']
  nlinarith

/-- **Sagitta bounds** `L²/(8R) ≤ s ≤ L²/(4R)`. -/
theorem sagitta_bounds (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L) (hLR : L ≤ 2 * R) :
    L ^ 2 / (8 * R) ≤ R - √(R ^ 2 - L ^ 2 / 4) ∧ R - √(R ^ 2 - L ^ 2 / 4) ≤ L ^ 2 / (4 * R) := by
  have hnn : 0 ≤ R ^ 2 - L ^ 2 / 4 := by nlinarith
  set q := √(R ^ 2 - L ^ 2 / 4) with hqdef
  have hq0 : 0 ≤ q := sqrt_nonneg _
  have hqR : q ≤ R := by
    rw [hqdef, sqrt_le_left hR.le]; nlinarith
  rw [sagitta_formula R L hR hL hLR]
  have hL2 : 0 ≤ L ^ 2 / 4 := by positivity
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

/-- **Fibonacci minimality** of the golden growth rate among `x² = px + q`, `p, q ≥ 1`. -/
theorem fibonacci_minimal (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    goldenRatio ≤ (p + √(p ^ 2 + 4 * q)) / 2 ∧
      (goldenRatio = (p + √(p ^ 2 + 4 * q)) / 2 ↔ p = 1 ∧ q = 1) := by
  have hs : √5 ≤ √(p ^ 2 + 4 * q) := sqrt_le_sqrt (by nlinarith)
  refine ⟨by rw [goldenRatio]; linarith, ⟨fun h => ?_, fun ⟨h1, h2⟩ => ?_⟩⟩
  · rw [goldenRatio] at h
    have hp1 : p = 1 := by linarith
    have hs' : √(p ^ 2 + 4 * q) = √5 := by linarith
    have h5 : p ^ 2 + 4 * q = 5 := by
      have := congrArg (· ^ 2) hs'
      simp only [sq_sqrt (show (0:ℝ) ≤ p ^ 2 + 4 * q by positivity),
        sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)] at this
      exact this
    refine ⟨hp1, ?_⟩
    rw [hp1] at h5; linarith
  · subst h1; subst h2; rw [goldenRatio]; norm_num

section Scalar
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Scalarisation flow** `B' = −γ(B − b̄)`. -/
theorem scalarisation (b B₀ : F) (γ s : ℝ) :
    HasDerivAt (fun t => b + exp (-γ * t) • (B₀ - b))
      (-γ • ((b + exp (-γ * s) • (B₀ - b)) - b)) s ∧
    ‖(b + exp (-γ * s) • (B₀ - b)) - b‖ = exp (-γ * s) * ‖B₀ - b‖ := by
  constructor
  · have h1 : HasDerivAt (fun t => -γ * t) (-γ) s := by
      simpa using (hasDerivAt_id s).const_mul (-γ)
    have h2 := (h1.exp.smul_const (B₀ - b)).const_add b
    convert h2 using 1
    rw [add_sub_cancel_left, smul_smul, mul_comm]
  · rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (exp_pos _).le]

end Scalar

end FBS3R.Selector
