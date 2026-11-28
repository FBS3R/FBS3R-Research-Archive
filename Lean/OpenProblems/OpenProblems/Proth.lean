import OpenProblems.Prelude
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Basic

/-!
# Proth's theorem

Listed as not yet formalized in Mathlib's `docs/1000.yaml` ("Proth's theorem").

Let `N = k·2^n + 1` with `0 < k < 2^n`. If some `a` satisfies `a^((N-1)/2) ≡ -1 (mod N)`,
then `N` is prime.

Proof: for a prime `p ∣ N`, `x = a^k` has multiplicative order exactly `2^n` modulo `p`, so
`2^n ∣ p - 1` and `p > 2^n`. Since `N < (2^n + 1)^2`, a composite `N` would have a prime factor
`p ≤ √N ≤ 2^n`.
-/

namespace OpenProblems.Proth

theorem proth (k n : ℕ) (hk : 0 < k) (hkn : k < 2 ^ n) (a : ℕ)
    (ha : (a : ZMod (k * 2 ^ n + 1)) ^ ((k * 2 ^ n + 1 - 1) / 2) = -1) :
    (k * 2 ^ n + 1).Prime := by
  set N := k * 2 ^ n + 1 with hN
  -- `n ≥ 1`
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · simp at hkn; omega
    · exact ⟨m, rfl⟩
  have hexp : (N - 1) / 2 = k * 2 ^ m := by
    rw [hN, Nat.add_sub_cancel, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num)]
  rw [hexp] at ha
  have hN2 : 2 ≤ N := by have : 0 < 2 ^ (m + 1) := by positivity
                         nlinarith
  -- every prime factor exceeds `2^(m+1)`
  have key : ∀ p : ℕ, p.Prime → p ∣ N → 2 ^ (m + 1) < p := by
    intro p hp hpN
    haveI := Fact.mk hp
    let f : ZMod N →+* ZMod p := ZMod.castHom hpN (ZMod p)
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ N := hpN
      rw [hN, pow_succ, ← mul_assoc, Nat.dvd_add_right (dvd_mul_left 2 _)] at this
      norm_num at this
    have hm1 : (-1 : ZMod p) ≠ 1 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_ofNat]; linear_combination -h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    set x : ZMod p := (a : ZMod p) ^ k
    have hx : x ^ 2 ^ m = -1 := by
      have := congrArg f ha
      rw [map_pow, map_neg, map_one, map_natCast] at this
      rw [← this, ← pow_mul]
    have hx1 : x ^ 2 ^ (m + 1) = 1 := by
      rw [pow_succ, pow_mul, hx]; norm_num
    have hord : orderOf x = 2 ^ (m + 1) :=
      orderOf_eq_prime_pow (by rw [hx]; exact hm1) hx1
    have hx0 : x ≠ 0 := by
      intro h; rw [h, zero_pow (by positivity)] at hx1; exact zero_ne_one hx1
    have hdvd := ZMod.orderOf_dvd_card_sub_one hx0
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by have := hp.two_le; omega) hdvd
    omega
  by_contra hnp
  have hmin := Nat.minFac_sq_le_self (by omega) hnp
  have hp := key _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd N)
  have h1 : (2 ^ (m + 1) + 1) ^ 2 ≤ N.minFac ^ 2 := Nat.pow_le_pow_left hp 2
  have h2 : N < (2 ^ (m + 1) + 1) ^ 2 := by
    rw [hN]; nlinarith
  omega

/-- Sanity check: `13 = 3·2^2 + 1` with witness `a = 2`. -/
example : Nat.Prime 13 := proth 3 2 (by norm_num) (by norm_num) 2 (by decide)

end OpenProblems.Proth
