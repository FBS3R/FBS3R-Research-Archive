import OpenProblems.Prelude
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Erdős Problem 318: a set with exactly one even element fails property `P₁`

Source: `formal-conjectures`, `ErdosProblems/318.lean`,
theorem `erdos_318.variants.contain_single_even` (category `research solved`, proof `sorry`).
The observation is credited by Sattler [Sa82] to Erdős.

Proof idea: put `f = 1` on the even element `e` and `f = -1` elsewhere. A vanishing signed sum
must contain `e` and gives `1/e = ∑ 1/n` over odd `n`; clearing the odd denominators
`P = ∏ n` gives `P = e · K`, so `P` would be even.
-/

namespace OpenProblems.Erdos318

/-- Verbatim from formal-conjectures. -/
def P₁ (A : Set ℕ) : Prop := ∀ (f : ℕ → ℝ),
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => 1) →
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => - 1) →
  Set.range f ⊆ {1, -1} →
  ∃ S : Finset ℕ, S.Nonempty ∧ ↑S ⊆ A \ {0} ∧ ∑ n ∈ S, f n / n = 0

/-- Key arithmetic lemma: `1 / e` (with `e` even) is never a sum of reciprocals of odd numbers. -/
theorem one_div_even_ne_sum_odd (e : ℕ) (he : Even e) (he0 : e ≠ 0) (T : Finset ℕ)
    (hT : ∀ n ∈ T, Odd n) : (1 : ℝ) / e ≠ ∑ n ∈ T, (1 : ℝ) / n := by
  intro h
  set P : ℕ := ∏ n ∈ T, n with hP
  have hPodd : Odd P := by
    rw [hP]; exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one hT
  have hdvd : ∀ n ∈ T, n ∣ P := fun n hn => Finset.dvd_prod_of_mem _ hn
  have hne : ∀ n ∈ T, (n : ℝ) ≠ 0 := fun n hn => by
    have := (hT n hn).pos; positivity
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he0
  -- multiply by `P`
  have key : (P : ℝ) / e = ((∑ n ∈ T, P / n : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    have : (P : ℝ) / e = P * (1 / e) := by ring
    rw [this, h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Nat.cast_div (hdvd n hn) (hne n hn)]
    ring
  set K : ℕ := ∑ n ∈ T, P / n
  have hPK : (P : ℝ) = e * K := by
    rw [← key]; field_simp
  have hPK' : P = e * K := by exact_mod_cast hPK
  have : Even P := hPK' ▸ he.mul_right K
  exact (Nat.not_even_iff_odd.2 hPodd) this

/-- **First formal proof** of `erdos_318.variants.contain_single_even`. -/
theorem erdos_318_contain_single_even {A : Set ℕ} (hA : A.Infinite)
    (hA' : {n | n ∈ A \ {0} ∧ Even n}.ncard = 1) : ¬ P₁ A := by
  obtain ⟨e, he⟩ := Set.ncard_eq_one.1 hA'
  have heA : e ∈ A \ {0} ∧ Even e := by
    have : e ∈ {n | n ∈ A \ {0} ∧ Even n} := he ▸ rfl
    exact this
  have hodd : ∀ n ∈ A \ {0}, n ≠ e → Odd n := by
    intro n hn hne
    by_contra hno
    have : n ∈ {n | n ∈ A \ {0} ∧ Even n} := ⟨hn, Nat.not_odd_iff_even.1 hno⟩
    rw [he] at this
    exact hne this
  -- an element of `A \ {0}` different from `e`
  obtain ⟨b, hbA, hb⟩ : ∃ b ∈ A, b ∉ ({0, e} : Set ℕ) :=
    (hA.diff (Set.toFinite {0, e})).nonempty
  have hb0 : b ≠ 0 := fun h => hb (by simp [h])
  have hbe : b ≠ e := fun h => hb (by simp [h])
  intro hP
  let f : ℕ → ℝ := fun n => if n = e then 1 else -1
  obtain ⟨S, hS, hSA, hsum⟩ := hP f
    (by
      intro h
      have := congrFun h ⟨b, hbA, by simpa using hb0⟩
      simp [f, hbe] at this
      norm_num at this)
    (by
      intro h
      have := congrFun h ⟨e, heA.1⟩
      simp [f] at this
      norm_num at this)
    (by rintro _ ⟨n, rfl⟩; by_cases h : n = e <;> simp [f, h])
  have hSpos : ∀ n ∈ S, (0 : ℝ) < n := fun n hn => by
    have := (hSA hn).2; simp at this; positivity
  by_cases heS : e ∈ S
  · rw [← Finset.add_sum_erase _ _ heS] at hsum
    have h1 : ∑ x ∈ S.erase e, f x / x = - ∑ x ∈ S.erase e, (1 : ℝ) / x := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun n hn => ?_
      simp [f, Finset.ne_of_mem_erase hn, neg_div]
    rw [h1] at hsum
    simp only [f, if_pos rfl] at hsum
    apply one_div_even_ne_sum_odd e heA.2 (by simpa using heA.1.2) (S.erase e)
      (fun n hn => hodd n (hSA (Finset.mem_of_mem_erase hn)) (Finset.ne_of_mem_erase hn))
    linarith
  · have : ∑ n ∈ S, f n / n < 0 := by
      apply Finset.sum_neg _ hS
      intro n hn
      have hne : n ≠ e := fun h => heS (h ▸ hn)
      simp only [f, if_neg hne]
      have := hSpos n hn
      rw [neg_div]; exact neg_neg_of_pos (by positivity)
    linarith

end OpenProblems.Erdos318
