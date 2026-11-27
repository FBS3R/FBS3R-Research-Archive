import OpenProblems.Prelude
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Lamé's theorem on the Euclidean algorithm

Listed as not yet formalized in Mathlib's `docs/1000.yaml` ("Lamé's theorem").

The number of division steps of the Euclidean algorithm on `(a, b)` with `a > b` is at most
five times the number of decimal digits of `b`. The proof goes through the classical
Fibonacci bound: `k + 1` steps force `b ≥ F_{k+2}` and `a ≥ F_{k+3}`, and `F_{n+5} ≥ 10 F_n`.
-/

namespace OpenProblems.Lame

/-- Number of division steps performed by the Euclidean algorithm on `(a, b)`. -/
def steps : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, b + 1 => 1 + steps (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

theorem steps_zero (a : ℕ) : steps a 0 = 0 := by rw [steps]

theorem steps_pos {a b : ℕ} (hb : 0 < b) : steps a b = 1 + steps b (a % b) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [steps]

/-- **Fibonacci bound**: `k + 1` steps with `a > b` force `F_{k+2} ≤ b` and `F_{k+3} ≤ a`. -/
theorem fib_le_of_steps : ∀ k a b : ℕ, b < a → steps a b = k + 1 →
    Nat.fib (k + 2) ≤ b ∧ Nat.fib (k + 3) ≤ a := by
  intro k
  induction k with
  | zero =>
    intro a b hab hs
    have hb : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | h
      · rw [steps_zero] at hs; omega
      · exact h
    simp [Nat.fib_add_two]; omega
  | succ k ih =>
    intro a b hab hs
    have hb : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | h
      · rw [steps_zero] at hs; omega
      · exact h
    rw [steps_pos hb] at hs
    have h := ih b (a % b) (Nat.mod_lt _ hb) (by omega)
    refine ⟨h.2, ?_⟩
    have hdiv : b + a % b ≤ a := by
      have h1 := Nat.div_add_mod a b
      have h2 : 1 ≤ a / b := (Nat.one_le_div_iff hb).2 hab.le
      nlinarith
    have : Nat.fib (k + 1 + 3) = Nat.fib (k + 3) + Nat.fib (k + 2) := by
      rw [show k + 1 + 3 = (k + 2) + 2 by ring, Nat.fib_add_two]; ring_nf
    omega

theorem fib_add_five_ge (n : ℕ) (hn : 2 ≤ n) : 10 * Nat.fib n ≤ Nat.fib (n + 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e : ∀ j, Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := fun j => Nat.fib_add_two
  have h1 := e m; have h2 := e (m + 1); have h3 := e (m + 2); have h4 := e (m + 3)
  have h5 := e (m + 4); have h6 := e (m + 5)
  have hmono : Nat.fib m ≤ Nat.fib (m + 1) := Nat.fib_mono (by omega)
  simp only [show m + 1 + 1 = m + 2 by ring, show m + 2 + 1 = m + 3 by ring,
    show m + 3 + 1 = m + 4 by ring, show m + 4 + 1 = m + 5 by ring,
    show m + 5 + 1 = m + 6 by ring, show m + 1 + 2 = m + 3 by ring,
    show m + 2 + 2 = m + 4 by ring, show m + 3 + 2 = m + 5 by ring,
    show m + 4 + 2 = m + 6 by ring, show m + 5 + 2 = m + 7 by ring,
    show m + 2 + 5 = m + 7 by ring] at *
  omega

theorem ten_pow_le_fib (d : ℕ) : 10 ^ d ≤ Nat.fib (5 * d + 2) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have := fib_add_five_ge (5 * d + 2) (by omega)
    rw [show 5 * (d + 1) + 2 = 5 * d + 2 + 5 by ring, pow_succ]
    omega

/-- **Lamé's theorem.** -/
theorem lame (a b : ℕ) (hab : b < a) : steps a b ≤ 5 * (Nat.digits 10 b).length := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [steps_zero]
  obtain ⟨k, hk⟩ : ∃ k, steps a b = k + 1 := ⟨steps a b - 1, by rw [steps_pos hb]; omega⟩
  have hfib := (fib_le_of_steps k a b hab hk).1
  have hlt : b < 10 ^ (Nat.digits 10 b).length := Nat.lt_base_pow_length_digits (by norm_num)
  by_contra hcon
  push_neg at hcon
  set d := (Nat.digits 10 b).length
  have : Nat.fib (5 * d + 2) ≤ Nat.fib (k + 2) := Nat.fib_mono (by omega)
  have := ten_pow_le_fib d
  omega

end OpenProblems.Lame
