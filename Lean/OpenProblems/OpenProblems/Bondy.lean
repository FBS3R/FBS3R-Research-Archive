import OpenProblems.Prelude
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Algebra.Field.ZMod

/-!
# Bondy's theorem on distinguishing sets

Listed as not yet formalized in Mathlib's `docs/1000.yaml` ("Bondy's theorem").

**Bondy (1972).** If `S₁, …, Sₙ` are `n` distinct subsets of an `n`-element set `X`, then some
element `x ∈ X` can be deleted from all of them while keeping them pairwise distinct.

Proof (linear algebra over `𝔽₂`): otherwise every `x` has a pair `(iₓ, jₓ)` with
`Sᵢ Δ Sⱼ = {x}`. The `n` vectors `e_{iₓ} + e_{jₓ} ∈ 𝔽₂ⁿ` map, under `e_i ↦ 𝟙_{Sᵢ}`, onto the
standard basis of `𝔽₂^X`, so they are linearly independent; but they all lie in the
`(n-1)`-dimensional hyperplane `∑ cᵢ = 0`.
-/

namespace OpenProblems.Bondy

instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open Finset

/-- Characteristic vector over `𝔽₂`. -/
def χ {n : ℕ} (s : Finset (Fin n)) : Fin n → ZMod 2 := fun y => if y ∈ s then 1 else 0

theorem chi_add_of_erase_eq {n : ℕ} {s t : Finset (Fin n)} {x : Fin n}
    (h : s.erase x = t.erase x) (hst : s ≠ t) : χ s + χ t = Pi.single x 1 := by
  have hx : (x ∈ s ∧ x ∉ t) ∨ (x ∉ s ∧ x ∈ t) := by
    by_cases hs : x ∈ s <;> by_cases ht : x ∈ t
    · exact absurd (by rw [← insert_erase hs, ← insert_erase ht, h]) hst
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, ht⟩
    · exact absurd (by rw [← erase_eq_of_notMem hs, ← erase_eq_of_notMem ht, h]) hst
  funext y
  simp only [Pi.add_apply, χ]
  by_cases hy : y = x
  · subst hy
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  · have : y ∈ s ↔ y ∈ t := by
      have := congrArg (y ∈ ·) h
      simpa [mem_erase, hy] using this
    rw [Pi.single_eq_of_ne hy]
    by_cases hys : y ∈ s
    · rw [if_pos hys, if_pos (this.1 hys)]; decide
    · rw [if_neg hys, if_neg (fun h => hys (this.2 h))]; simp

/-- **Bondy's theorem.** -/
theorem bondy {n : ℕ} (hn : 0 < n) (S : Fin n → Finset (Fin n)) (hS : Function.Injective S) :
    ∃ x : Fin n, Function.Injective (fun i => (S i).erase x) := by
  by_contra hcon
  push_neg at hcon
  have : ∀ x : Fin n, ∃ i j : Fin n, (S i).erase x = (S j).erase x ∧ i ≠ j := by
    intro x
    have := hcon x
    simp only [Function.Injective, not_forall] at this
    obtain ⟨i, j, hij, hne⟩ := this
    exact ⟨i, j, hij, hne⟩
  choose I J hIJ hne using this
  let φ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    Fintype.linearCombination (ZMod 2) (fun i => χ (S i))
  let σ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    Fintype.linearCombination (ZMod 2) (fun _ => (1 : ZMod 2))
  let w : Fin n → (Fin n → ZMod 2) := fun x => Pi.single (I x) 1 + Pi.single (J x) 1
  have hφ : ∀ i, φ (Pi.single i 1) = χ (S i) := by
    intro i
    simp only [φ, Fintype.linearCombination_apply]
    rw [sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  have hσ : ∀ i, σ (Pi.single i 1) = 1 := by
    intro i
    simp only [σ, Fintype.linearCombination_apply, smul_eq_mul, mul_one]
    rw [sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  have hφw : φ ∘ w = fun x => Pi.single x 1 := by
    funext x
    simp only [Function.comp, w, map_add, hφ]
    exact chi_add_of_erase_eq (hIJ x) (fun h => hne x (hS h))
  have hw : LinearIndependent (ZMod 2) w :=
    LinearIndependent.of_comp φ (hφw ▸ Pi.linearIndependent_single_one (Fin n) (ZMod 2))
  have hwker : ∀ x, w x ∈ LinearMap.ker σ := by
    intro x
    simp only [LinearMap.mem_ker, w, map_add, hσ]
    decide
  let w' : Fin n → LinearMap.ker σ := fun x => ⟨w x, hwker x⟩
  have hw' : LinearIndependent (ZMod 2) w' :=
    LinearIndependent.of_comp (LinearMap.ker σ).subtype (by exact hw)
  have hcard := hw'.fintype_card_le_finrank
  have hrank := LinearMap.finrank_range_add_finrank_ker σ
  have hrange : Module.finrank (ZMod 2) (LinearMap.range σ) = 1 := by
    have : LinearMap.range σ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨c • Pi.single ⟨0, hn⟩ 1, by rw [map_smul, hσ, smul_eq_mul, mul_one]⟩
    rw [this, finrank_top, Module.finrank_self]
  simp only [Fintype.card_fin, Module.finrank_fin_fun] at hcard hrank
  omega

end OpenProblems.Bondy
