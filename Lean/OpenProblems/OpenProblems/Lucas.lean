import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.PowMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Lucas–Pratt primality certificates

A small, reusable interface to `lucas_primality` that only asks for computations on natural
numbers of the form `a ^ b % p`, which `norm_num` evaluates by fast modular exponentiation.
Primality of the prime factors of `p - 1` is supplied as a list, so certificates can be nested.
-/

namespace OpenProblems

/-- A prime dividing the product of a list of primes belongs to the list. -/
theorem mem_of_prime_dvd_prod {q : ℕ} (hq : q.Prime) :
    ∀ (L : List ℕ), (∀ x ∈ L, x.Prime) → q ∣ L.prod → q ∈ L
  | [], _, h => by
      simp only [List.prod_nil, Nat.dvd_one] at h
      exact absurd h hq.one_lt.ne'
  | x :: L, hL, h => by
      rw [List.prod_cons] at h
      rcases (Nat.Prime.dvd_mul hq).1 h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hq (hL x (by simp))).1 h
        simp [this]
      · exact List.mem_cons_of_mem _
          (mem_of_prime_dvd_prod hq L (fun y hy => hL y (List.mem_cons_of_mem _ hy)) h)

/-- **Lucas' primality test**, phrased with natural-number modular powers.
`L` is the list of prime factors (with multiplicity allowed) whose product is `p - 1`. -/
theorem prime_of_lucas (p a : ℕ) (L : List ℕ) (hp : 1 < p) (hprod : L.prod = p - 1)
    (hL : ∀ x ∈ L, x.Prime) (ha : a ^ (p - 1) % p = 1)
    (hd : ∀ q ∈ L, a ^ ((p - 1) / q) % p ≠ 1) : p.Prime := by
  have hp1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt hp
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · rw [← Nat.cast_pow, ← ZMod.natCast_mod, ha, Nat.cast_one]
  · intro q hq hqd h
    have hqL : q ∈ L := mem_of_prime_dvd_prod hq L hL (hprod ▸ hqd)
    apply hd q hqL
    have h' := (ZMod.natCast_eq_natCast_iff' (a ^ ((p - 1) / q)) 1 p).1 (by push_cast; exact h)
    rwa [hp1] at h'

/-- Modular exponentiation by repeated squaring, with a structural fuel parameter so that the
kernel can evaluate it (using its GMP-accelerated `Nat` arithmetic). When the fuel runs out it
falls back to the definition, so it is correct for every value of the fuel. -/
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => a ^ b % m
  | f + 1, a, b =>
    if b = 0 then 1 % m
    else
      let r := powMod m f (a * a % m) (b / 2)
      if b % 2 = 0 then r else r * a % m

theorem powMod_eq (m : ℕ) : ∀ f a b, powMod m f a b = a ^ b % m
  | 0, a, b => rfl
  | f + 1, a, b => by
    simp only [powMod]
    rw [powMod_eq m f]
    by_cases hb : b = 0
    · simp [hb]
    · simp only [hb, ↓reduceIte]
      have hsq : (a * a % m) ^ (b / 2) % m = a ^ (2 * (b / 2)) % m := by
        rw [← Nat.pow_mod, pow_mul, sq]
      by_cases h2 : b % 2 = 0
      · simp only [h2, ↓reduceIte]; rw [hsq]
        congr 1; congr 1; omega
      · simp only [h2, ↓reduceIte]; rw [hsq, Nat.mod_mul_mod, ← pow_succ]
        congr 1; congr 1; omega

/-- Lucas' test with the modular powers computed by `powMod` (to be discharged by
`decide +kernel`). -/
theorem prime_of_lucas' (p a : ℕ) (L : List ℕ) (hp : 1 < p) (hprod : L.prod = p - 1)
    (hL : ∀ x ∈ L, x.Prime) (ha : powMod p 128 a (p - 1) = 1)
    (hd : ∀ q ∈ L, powMod p 128 a ((p - 1) / q) ≠ 1) : p.Prime := by
  rw [powMod_eq] at ha
  exact prime_of_lucas p a L hp hprod hL ha (fun q hq => by have := hd q hq; rwa [powMod_eq] at this)

end OpenProblems
