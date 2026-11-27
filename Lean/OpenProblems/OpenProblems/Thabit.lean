import OpenProblems.Prelude
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Thābit ibn Qurra's theorem on amicable numbers

Listed as not yet formalized in Mathlib's `docs/1000.yaml` ("Thabit ibn Qurra's theorem").

If `n ≥ 2` and `p = 3·2^{n-1} - 1`, `q = 3·2^n - 1`, `r = 9·2^{2n-1} - 1` are all prime, then
`a = 2^n p q` and `b = 2^n r` form an amicable pair: `s(a) = b` and `s(b) = a`, where `s` is the
sum of proper divisors.

We write `n = m + 1` and `t = 2^m`, so that `p = 3t - 1`, `q = 6t - 1`, `r = 18t² - 1`.
-/

namespace OpenProblems.Thabit

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem sum_two_pow (k : ℕ) : (∑ i ∈ Finset.range k, 2 ^ i) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem sigma_two_pow (k : ℕ) : σ 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two, sum_two_pow]

theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (i := 1) hp
  simp only [pow_one] at this
  rw [this]; simp [Finset.sum_range_succ, add_comm]

theorem coprime_two_pow_of_odd {p : ℕ} (k : ℕ) (hp : Odd p) : Nat.Coprime (2 ^ k) p :=
  Nat.Coprime.pow_left k ((Nat.coprime_two_left).2 hp)

/-- **Thābit ibn Qurra's theorem**, in terms of `σ₁`: `σ(a) = σ(b) = a + b`. -/
theorem thabit_sigma (m : ℕ) (hm : 1 ≤ m)
    (hp : (3 * 2 ^ m - 1).Prime) (hq : (6 * 2 ^ m - 1).Prime)
    (hr : (18 * (2 ^ m) ^ 2 - 1).Prime) :
    σ 1 (2 ^ (m + 1) * (3 * 2 ^ m - 1) * (6 * 2 ^ m - 1)) =
        2 ^ (m + 1) * (3 * 2 ^ m - 1) * (6 * 2 ^ m - 1) + 2 ^ (m + 1) * (18 * (2 ^ m) ^ 2 - 1) ∧
    σ 1 (2 ^ (m + 1) * (18 * (2 ^ m) ^ 2 - 1)) =
        2 ^ (m + 1) * (3 * 2 ^ m - 1) * (6 * 2 ^ m - 1) + 2 ^ (m + 1) * (18 * (2 ^ m) ^ 2 - 1) := by
  set t := 2 ^ m with ht
  clear_value t
  have ht2 : 2 ≤ t := by
    rw [ht]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
  have e1 : 3 * (u + 2) - 1 = 3 * u + 5 := by omega
  have e2 : 6 * (u + 2) - 1 = 6 * u + 11 := by omega
  have e3 : 18 * (u + 2) ^ 2 - 1 = 18 * u ^ 2 + 72 * u + 71 := by
    have : 18 * (u + 2) ^ 2 = 18 * u ^ 2 + 72 * u + 72 := by ring
    omega
  rw [e1] at hp ⊢; rw [e2] at hq ⊢; rw [e3] at hr ⊢
  have h2 : 2 ^ (m + 1) = 2 * (u + 2) := by rw [pow_succ, ← ht]; ring
  have hs2 : σ 1 (2 ^ (m + 1)) = 4 * u + 7 := by
    have := sigma_two_pow (m + 1)
    rw [show 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) by ring] at this
    rw [h2] at this ⊢; omega
  have hodd : ∀ x, Odd (2 * x + 1) := fun x => ⟨x, rfl⟩
  have op : Odd (3 * u + 5) := hp.odd_of_ne_two (by omega)
  have oq : Odd (6 * u + 11) := ⟨3 * u + 5, by ring⟩
  have or' : Odd (18 * u ^ 2 + 72 * u + 71) := ⟨9 * u ^ 2 + 36 * u + 35, by ring⟩
  have cpq : Nat.Coprime (2 ^ (m + 1) * (3 * u + 5)) (6 * u + 11) := by
    refine Nat.coprime_mul_iff_left.2 ⟨coprime_two_pow_of_odd _ oq, ?_⟩
    rw [Nat.coprime_primes hp hq]; omega
  refine ⟨?_, ?_⟩
  · rw [isMultiplicative_sigma.map_mul_of_coprime cpq,
      isMultiplicative_sigma.map_mul_of_coprime (coprime_two_pow_of_odd _ op), hs2,
      sigma_prime hp, sigma_prime hq, h2]
    ring
  · rw [isMultiplicative_sigma.map_mul_of_coprime (coprime_two_pow_of_odd _ or'), hs2,
      sigma_prime hr, h2]
    ring

/-- **Thābit ibn Qurra's theorem** (amicable form): with `s(x) = ∑_{d ∣ x, d < x} d`,
`s(a) = b` and `s(b) = a`. -/
theorem thabit (m : ℕ) (hm : 1 ≤ m)
    (hp : (3 * 2 ^ m - 1).Prime) (hq : (6 * 2 ^ m - 1).Prime)
    (hr : (18 * (2 ^ m) ^ 2 - 1).Prime) :
    let a := 2 ^ (m + 1) * (3 * 2 ^ m - 1) * (6 * 2 ^ m - 1)
    let b := 2 ^ (m + 1) * (18 * (2 ^ m) ^ 2 - 1)
    ∑ d ∈ a.properDivisors, d = b ∧ ∑ d ∈ b.properDivisors, d = a := by
  intro a b
  obtain ⟨h1, h2⟩ := thabit_sigma m hm hp hq hr
  replace h1 : σ 1 a = a + b := h1
  replace h2 : σ 1 b = a + b := h2
  have ha := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := a)
  have hb := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := b)
  rw [← sigma_one_apply] at ha hb
  constructor <;> omega

/-- Sanity check: `m = 1` gives the classical pair `(220, 284)`. -/
example : ∑ d ∈ (220 : ℕ).properDivisors, d = 284 ∧ ∑ d ∈ (284 : ℕ).properDivisors, d = 220 :=
  thabit 1 le_rfl (by norm_num) (by norm_num) (by norm_num)

end OpenProblems.Thabit
