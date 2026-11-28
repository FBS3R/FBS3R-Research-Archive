import OpenProblems.Prelude
import OpenProblems.Lucas
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum.GCD

/-!
# A 2-hyperperfect number not of McCranie's form `3^m (3^{m+1} - 2)`

Source: `formal-conjectures`, `Wikipedia/HyperperfectNumber.lean`,
theorem `two_hyperperfect_characterization` (category `research solved`, proof `sorry`).
The counterexample is due to Alexander Violette (June 2026, OEIS A007593):
`n = 3^16 · 129140227 · 256572153302107 · 225205396855537107298933866373`.

We give a complete machine-checked proof: the three large factors are certified prime with
nested Lucas–Pratt certificates, the divisor sum is computed via multiplicativity of `σ₁`,
and the representation `n = 3^m (3^{m+1} - 2)` is excluded for every `m`.
-/

namespace OpenProblems.Hyperperfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Verbatim from formal-conjectures: `n > 1` is `k`-hyperperfect. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ 1 < n ∧ n = 1 + k * ((∑ d ∈ n.properDivisors, d) - 1)

theorem prime_12211 : Nat.Prime 12211 := by norm_num
theorem prime_22346131 : Nat.Prime 22346131 := by norm_num
theorem prime_894301 : Nat.Prime 894301 := by norm_num
theorem prime_11047 : Nat.Prime 11047 := by norm_num
theorem prime_7489 : Nat.Prime 7489 := by norm_num
theorem prime_14029501 : Nat.Prime 14029501 := by norm_num

theorem prime_q1 : Nat.Prime 129140227 :=
  prime_of_lucas' 129140227 5 [2, 3, 3, 19, 107, 3529] (by norm_num) (by decide +kernel)
    (by simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          and_true]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (by decide +kernel) (by decide +kernel)

theorem prime_137002507849 : Nat.Prime 137002507849 :=
  prime_of_lucas' 137002507849 29 [2, 2, 2, 3, 3, 23, 11047, 7489] (by norm_num) (by decide +kernel)
    (by simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          and_true]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_11047, prime_7489⟩)
    (by decide +kernel) (by decide +kernel)

theorem prime_153174091919 : Nat.Prime 153174091919 :=
  prime_of_lucas' 153174091919 7 [2, 53, 103, 14029501] (by norm_num) (by decide +kernel)
    (by simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          and_true]
        exact ⟨by norm_num, by norm_num, by norm_num, prime_14029501⟩)
    (by decide +kernel) (by decide +kernel)

theorem prime_q2 : Nat.Prime 256572153302107 :=
  prime_of_lucas' 256572153302107 2 [2, 3, 991, 1931, 22346131] (by norm_num) (by decide +kernel)
    (by simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          and_true]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_22346131⟩)
    (by decide +kernel) (by decide +kernel)

theorem prime_q3 : Nat.Prime 225205396855537107298933866373 :=
  prime_of_lucas' 225205396855537107298933866373 2 [2, 2, 3, 894301, 137002507849, 153174091919] (by norm_num) (by decide +kernel)
    (by simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          and_true]
        exact ⟨by norm_num, by norm_num, by norm_num, prime_894301, prime_137002507849, prime_153174091919⟩)
    (by decide +kernel) (by decide +kernel)

/-- Violette's number. -/
def N : ℕ := 3 ^ 16 * 129140227 * 256572153302107 * 225205396855537107298933866373

theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (i := 1) hp
  simp only [pow_one] at this
  rw [this]; simp [Finset.sum_range_succ, add_comm]

theorem sigma_form {a q₁ q₂ q₃ : ℕ} (h₁ : q₁.Prime) (h₂ : q₂.Prime) (h₃ : q₃.Prime)
    (c₁ : Nat.Coprime a q₁) (c₂ : Nat.Coprime (a * q₁) q₂) (c₃ : Nat.Coprime (a * q₁ * q₂) q₃) :
    σ 1 (a * q₁ * q₂ * q₃) = σ 1 a * (q₁ + 1) * (q₂ + 1) * (q₃ + 1) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime c₃, isMultiplicative_sigma.map_mul_of_coprime c₂,
    isMultiplicative_sigma.map_mul_of_coprime c₁, sigma_prime h₁, sigma_prime h₂, sigma_prime h₃]

theorem sigma_N : σ 1 N = (∑ k ∈ Finset.range 17, 3 ^ k) * (129140227 + 1) *
    (256572153302107 + 1) * (225205396855537107298933866373 + 1) := by
  have h3 : σ 1 (3 ^ 16) = ∑ k ∈ Finset.range 17, 3 ^ k :=
    sigma_one_apply_prime_pow Nat.prime_three
  have c1 : Nat.Coprime (3 ^ 16) 129140227 := by unfold Nat.Coprime; decide +kernel
  have c2 : Nat.Coprime (3 ^ 16 * 129140227) 256572153302107 := by
    unfold Nat.Coprime; decide +kernel
  have c3 : Nat.Coprime (3 ^ 16 * 129140227 * 256572153302107)
      225205396855537107298933866373 := by unfold Nat.Coprime; decide +kernel
  have := sigma_form prime_q1 prime_q2 prime_q3 c1 c2 c3
  rw [h3] at this
  exact this

theorem N_eq : N = 321210648228113097833688328004214356646685508531160153551637 := by norm_num [N]

theorem sigma_N_eq : σ 1 N = 481815972342169646750532492006321534970028262796740230327456 := by
  rw [sigma_N]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num

theorem isHyperperfect_N : IsHyperperfect 2 N := by
  refine ⟨by norm_num, by rw [N_eq]; norm_num, ?_⟩
  have h := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := N)
  rw [← sigma_one_apply, sigma_N_eq] at h
  generalize ∑ d ∈ N.properDivisors, d = s at h ⊢
  rw [N_eq] at h ⊢
  omega

theorem N_not_mccranie : ∀ m : ℕ, N ≠ 3 ^ m * (3 ^ (m + 1) - 2) := by
  intro m hm
  have hle : m < 200 := by
    by_contra h
    push_neg at h
    have h1 : 3 ^ 200 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) h
    have h2 : 1 ≤ 3 ^ (m + 1) - 2 := by
      have : 3 ≤ 3 ^ (m + 1) := Nat.le_self_pow (by omega) 3
      omega
    have h3 : 3 ^ m ≤ N := hm ▸ Nat.le_mul_of_pos_right _ h2
    have : N < 3 ^ 200 := by norm_num [N]
    omega
  have key : ∀ m < 200, N ≠ 3 ^ m * (3 ^ (m + 1) - 2) := by
    unfold N; decide +kernel
  exact key m hle hm

/-- **First formal proof** of `two_hyperperfect_characterization` from formal-conjectures:
not every 2-hyperperfect number has the form `3^m (3^{m+1} - 2)` with `3^{m+1} - 2` prime. -/
theorem two_hyperperfect_characterization :
    ¬ ∀ n : ℕ, IsHyperperfect 2 n →
      ∃ m ≥ 1, (3 ^ (m + 1) - 2).Prime ∧ n = 3 ^ m * (3 ^ (m + 1) - 2) := by
  intro h
  obtain ⟨m, -, -, hm⟩ := h N isHyperperfect_N
  exact N_not_mccranie m hm

end OpenProblems.Hyperperfect
