/-
# Zeckendorf addresses of the constrained (PXP / Fibonacci) chain

Source: *Rational Spectral Hierarchies and Matrix-Free Gauge Certificates* (2026-10-23),
Proposition `prop:rank`: on the set `𝒞ₙ` of binary strings of length `n` with no two
adjacent ones, the address `r(s) = ∑ⱼ sⱼ F_{n-j+2}` is a bijection
`𝒞ₙ → {0, …, F_{n+2} - 1}`.

Machine-checked here (with `Nat.fib`, `F₁ = F₂ = 1`):
* `mem_C_iff` : the recursive set `C n` is exactly the strings of length `n` with no `11`;
* `rk_lt`, `rk_injOn`, `rk_surj` : the address is a bijection onto `range (F_{n+2})`;
* `card_C` : `|𝒞ₙ| = F_{n+2}` (the Hilbert-space dimension of the open PXP chain);
* `flip_changes_address` : flipping a permitted site `j` changes the address by `F_{n-j+2}`.
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

namespace FBS3R.Zeckendorf

open Nat Finset

/-- No two adjacent `true`s. -/
def NA : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => ¬(a = true ∧ b = true) ∧ NA (b :: l)

/-- The constrained configuration space, built recursively. -/
def C : ℕ → Finset (List Bool)
  | 0 => {[]}
  | 1 => {[false], [true]}
  | n + 2 => (C (n + 1)).image (List.cons false) ∪ (C n).image (fun l => true :: false :: l)

/-- The Zeckendorf address `r(s) = ∑ⱼ sⱼ F_{n-j+2}`. -/
def rk : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then fib (l.length + 2) else 0) + rk l

theorem length_of_mem : ∀ {n : ℕ} {l : List Bool}, l ∈ C n → l.length = n
  | 0, l, h => by simp [C] at h; simp [h]
  | 1, l, h => by simp [C] at h; rcases h with rfl | rfl <;> rfl
  | n + 2, l, h => by
    simp only [C, mem_union, mem_image] at h
    rcases h with ⟨l', h', rfl⟩ | ⟨l', h', rfl⟩
    · simp [length_of_mem h']
    · simp [length_of_mem h']

theorem mem_C_iff : ∀ (n : ℕ) (l : List Bool), l ∈ C n ↔ l.length = n ∧ NA l
  | 0, l => by cases l <;> simp [C, NA]
  | 1, l => by
    rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [C]
    · cases a <;> simp [C, NA]
    · simp [C]
  | n + 2, l => by
    constructor
    · intro h
      simp only [C, mem_union, mem_image] at h
      rcases h with ⟨l', h', rfl⟩ | ⟨l', h', rfl⟩
      · obtain ⟨h1, h2⟩ := (mem_C_iff (n + 1) l').mp h'
        refine ⟨by simp [h1], ?_⟩
        rcases l' with _ | ⟨c, l'⟩
        · simp at h1
        · exact ⟨by simp, h2⟩
      · obtain ⟨h1, h2⟩ := (mem_C_iff n l').mp h'
        refine ⟨by simp [h1], ⟨by simp, ?_⟩⟩
        rcases l' with _ | ⟨c, l'⟩
        · trivial
        · exact ⟨by simp, h2⟩
    · rintro ⟨h1, h2⟩
      rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
      · simp at h1
      · simp at h1
      · simp only [C, mem_union, mem_image]
        cases a
        · exact Or.inl ⟨b :: l, (mem_C_iff (n + 1) _).mpr ⟨by simpa using h1, h2.2⟩, rfl⟩
        · cases b
          · refine Or.inr ⟨l, (mem_C_iff n l).mpr ⟨by simpa using h1, ?_⟩, rfl⟩
            have h3 := h2.2
            rcases l with _ | ⟨c, l⟩
            · trivial
            · exact h3.2
          · exact absurd ⟨rfl, rfl⟩ h2.1

@[simp] theorem rk_false (l : List Bool) : rk (false :: l) = rk l := by simp [rk]
@[simp] theorem rk_true (l : List Bool) : rk (true :: l) = fib (l.length + 2) + rk l := by
  simp [rk]

theorem fib4 (n : ℕ) : fib (n + 4) = fib (n + 2) + fib (n + 3) := fib_add_two

theorem rk_lt : ∀ {n : ℕ} {l : List Bool}, l ∈ C n → rk l < fib (n + 2)
  | 0, l, h => by simp [C] at h; simp [h, rk]
  | 1, l, h => by simp [C] at h; rcases h with rfl | rfl <;> simp [rk, fib_add_two]
  | n + 2, l, h => by
    simp only [C, mem_union, mem_image] at h
    have e := fib4 n
    have e1 : fib (n + 1 + 2) = fib (n + 3) := rfl
    have e2 : fib (n + 2 + 2) = fib (n + 4) := rfl
    rcases h with ⟨l', h', rfl⟩ | ⟨l', h', rfl⟩
    · have := rk_lt h'
      simp only [rk_false]; omega
    · have := rk_lt h'
      have hl := length_of_mem h'
      simp only [rk_true, rk_false, List.length_cons, hl]
      omega

theorem rk_injOn : ∀ (n : ℕ), Set.InjOn rk (C n : Set (List Bool))
  | 0, l₁, h₁, l₂, h₂, _ => by simp [C] at h₁ h₂; simp [h₁, h₂]
  | 1, l₁, h₁, l₂, h₂, he => by
    simp [C] at h₁ h₂
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp_all [rk]
  | n + 2, l₁, h₁, l₂, h₂, he => by
    simp only [C, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at h₁ h₂
    rcases h₁ with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
      rcases h₂ with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · simp only [rk_false] at he
      rw [rk_injOn (n + 1) ha hc he]
    · exfalso
      have h1 := rk_lt ha
      have hl := length_of_mem hc
      simp only [rk_true, rk_false, List.length_cons, hl] at he
      omega
    · exfalso
      have h1 := rk_lt hc
      have hl := length_of_mem ha
      simp only [rk_true, rk_false, List.length_cons, hl] at he
      omega
    · have hl := length_of_mem ha
      have hl' := length_of_mem hc
      simp only [rk_true, rk_false, List.length_cons, hl, hl'] at he
      rw [rk_injOn n ha hc (by omega)]

theorem rk_surj : ∀ (n k : ℕ), k < fib (n + 2) → ∃ l ∈ C n, rk l = k
  | 0, k, hk => ⟨[], by simp [C], by simp [rk]; simp at hk; omega⟩
  | 1, k, hk => by
    have : fib 3 = 2 := rfl
    rw [this] at hk
    interval_cases k
    · exact ⟨[false], by simp [C], by simp [rk]⟩
    · exact ⟨[true], by simp [C], by simp [rk]⟩
  | n + 2, k, hk => by
    have e := fib4 n
    have e1 : fib (n + 1 + 2) = fib (n + 3) := rfl
    have e2 : fib (n + 2 + 2) = fib (n + 4) := rfl
    by_cases h : k < fib (n + 3)
    · obtain ⟨l, hl, rfl⟩ := rk_surj (n + 1) k h
      exact ⟨false :: l, by simp only [C, mem_union, mem_image]; exact Or.inl ⟨l, hl, rfl⟩,
        by simp⟩
    · obtain ⟨l, hl, hr⟩ := rk_surj n (k - fib (n + 3)) (by omega)
      refine ⟨true :: false :: l, by simp only [C, mem_union, mem_image]; exact Or.inr ⟨l, hl, rfl⟩,
        ?_⟩
      have hl' := length_of_mem hl
      simp only [rk_true, rk_false, List.length_cons, hl', hr]
      omega

theorem image_rk (n : ℕ) : (C n).image rk = range (fib (n + 2)) := by
  ext k; simp only [mem_image, mem_range]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact rk_lt hl
  · intro hk; exact rk_surj n k hk

/-- **The dimension of the constrained chain is `F_{n+2}`.** -/
theorem card_C (n : ℕ) : (C n).card = fib (n + 2) := by
  rw [← card_range (fib (n + 2)), ← image_rk n, card_image_of_injOn (rk_injOn n)]

/-- Address change of a flip: replacing `0` by `1` at a site with `m` sites to its right
raises the address by exactly `F_{m+2}` (that is `F_{n-j+2}` for site `j`). -/
theorem flip_changes_address (p q : List Bool) :
    rk (p ++ true :: q) = rk (p ++ false :: q) + fib (q.length + 2) := by
  induction p with
  | nil => simp; ring
  | cons b p ih =>
    simp only [List.cons_append, rk, List.length_append, List.length_cons, ih]; ring

end FBS3R.Zeckendorf
