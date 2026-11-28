import OpenProblems.Prelude
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Midy's theorem

Listed as not yet formalized in Mathlib's `docs/1000.yaml` ("Midy's theorem").

Let `p` be a prime, `b ≥ 2` a base and `0 < a < p`. If the period of `a/p` in base `b`
(the multiplicative order of `b` mod `p`) is even, `2k`, then the repetend
`R = a (b^{2k} - 1) / p` splits into two `k`-digit halves `R = A·b^k + B` with
`A + B = b^k - 1` (e.g. `1/7 = 0.(142857)` and `142 + 857 = 999`).
-/

namespace OpenProblems.Midy

theorem midy (p b a k : ℕ) [hp : Fact p.Prime] (hb : 2 ≤ b) (ha : 0 < a) (hap : a < p)
    (hord : orderOf (b : ZMod p) = 2 * k) :
    p ∣ a * (b ^ (2 * k) - 1) ∧
    ∃ A B : ℕ, A < b ^ k ∧ B < b ^ k ∧ a * (b ^ (2 * k) - 1) / p = A * b ^ k + B ∧
      A + B = b ^ k - 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨by simp, 0, 0, by simp⟩
  -- `b^k ≡ -1 (mod p)`
  set x : ZMod p := (b : ZMod p) ^ k
  have hx2 : x ^ 2 = 1 := by rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one hk h
    omega
  have hxm : x = -1 := by
    have : (x - 1) * (x + 1) = 0 := by ring_nf; rw [hx2]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hx1
    · exact eq_neg_of_add_eq_zero_left h
  have hdvd : p ∣ b ^ k + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [show (b : ZMod p) ^ k = x from rfl, hxm]
    ring
  obtain ⟨c, hc⟩ := hdvd
  have hbk : 1 ≤ b ^ k := Nat.one_le_pow _ _ (by omega)
  have hfac : b ^ (2 * k) - 1 = (b ^ k - 1) * (b ^ k + 1) := by
    rw [mul_comm 2 k, pow_mul]
    have : (b ^ k) ^ 2 = (b ^ k - 1) * (b ^ k + 1) + 1 := by
      obtain ⟨u, hu⟩ : ∃ u, b ^ k = u + 1 := ⟨b ^ k - 1, by omega⟩
      rw [hu]; simp; ring
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = a * c := ⟨_, rfl⟩
  have hR : a * (b ^ (2 * k) - 1) = p * (m * (b ^ k - 1)) := by
    rw [hfac, hc, hm]; ring
  have hp0 : 0 < p := hp.out.pos
  have hm1 : 1 ≤ m := by
    have : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h] at hc; simp at hc
      · exact h
    rw [hm]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ha.ne' this.ne')
  have hmle : m ≤ b ^ k := by
    -- `p * m = a (b^k + 1) < p (b^k + 1)`
    have h1 : p * m = a * (b ^ k + 1) := by rw [hm, hc]; ring
    have h2 : a * (b ^ k + 1) < p * (b ^ k + 1) := Nat.mul_lt_mul_of_pos_right hap (by omega)
    have : m < b ^ k + 1 := by
      by_contra h; push_neg at h
      have := Nat.mul_le_mul_left p h
      omega
    omega
  refine ⟨⟨_, hR⟩, m - 1, b ^ k - m, by omega, by omega, ?_, by omega⟩
  rw [hR, Nat.mul_div_cancel_left _ hp0]
  obtain ⟨u, rfl⟩ : ∃ u, m = u + 1 := ⟨m - 1, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, b ^ k = u + 1 + v := ⟨b ^ k - (u + 1), by omega⟩
  rw [hv]; simp only [Nat.add_sub_cancel]
  rw [show u + 1 + v - (u + 1) = v by omega, show u + 1 + v - 1 = u + v by omega]
  ring

/-- Example: `1/7 = 0.(142857)`, `142 + 857 = 999`. -/
example : 1 * (10 ^ 6 - 1) / 7 = 142 * 10 ^ 3 + 857 ∧ 142 + 857 = 10 ^ 3 - 1 := by norm_num

end OpenProblems.Midy
