/-
# Rational structure of the PXP moment generating functions

`g n β F` counts admissible arrays of `n` temporal trajectories (sites `1..n` of the chain)
whose flip sets are pairwise disjoint with union `F`, which satisfy the spatial blockade between
neighbouring sites, and whose last trajectory is `β`.  It is defined by the transfer recursion;
`Walks.lean` proves that it really counts these arrays.

The main algebraic result, `good_total`, says that for `k ≥ 1` the generating series
`T(z) = ∑ₙ (∑_β g n β univ) zⁿ` satisfies
`T(z) · (1 - z - z²)^(⌊k/2⌋+1) = P(z)` with `P ∈ ℤ[z]`, `deg P ≤ 3⌊k/2⌋ - 2`.
-/
import APEX.PXP.Trajectories
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.LinearCombination

namespace APEX.PXP

open Finset PowerSeries

variable {k : ℕ}

/-- Empty-prefix indicator. -/
def δ (n : ℕ) (F : Finset (Fin k)) : ℕ := if n = 0 ∧ F = ∅ then 1 else 0

/-- Transfer recursion for the number of admissible arrays of length `n` ending in `β` with
total flip set `F`. -/
def g : ℕ → Traj k → Finset (Fin k) → ℕ
  | 0, _, _ => 0
  | n + 1, β', F' =>
    if flips β' ⊆ F' then
      δ n (F' \ flips β') + ∑ β : Traj k, (if Compat β β' then g n β (F' \ flips β') else 0)
    else 0

lemma g_eq_zero_of_not_subset {n : ℕ} {β : Traj k} {F : Finset (Fin k)}
    (h : ¬ flips β ⊆ F) : g n β F = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [g, h]

/-- Generating series of `g · β F`. -/
noncomputable def G (β : Traj k) (F : Finset (Fin k)) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (g n β F : ℤ))

/-- Generating series of the empty-prefix indicator. -/
noncomputable def E (F : Finset (Fin k)) : PowerSeries ℤ := PowerSeries.mk (fun n => (δ n F : ℤ))

/-- Total series over all final trajectories. -/
noncomputable def T (F : Finset (Fin k)) : PowerSeries ℤ := ∑ β : Traj k, G β F

/-- Series over final trajectories that flip at least once. -/
noncomputable def A (F : Finset (Fin k)) : PowerSeries ℤ :=
  ∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty), G β F

/-- `D(z) = 1 - z - z²`. -/
noncomputable def Dp : Polynomial ℤ := 1 - Polynomial.X - Polynomial.X ^ 2

noncomputable def D : PowerSeries ℤ := 1 - X - X ^ 2

lemma coe_Dp : ((Dp : Polynomial ℤ) : PowerSeries ℤ) = D := by
  simp [Dp, D]

lemma natDegree_Dp_le : Dp.natDegree ≤ 2 := by
  unfold Dp
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  refine max_le ((Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_
  · simp
  · simp
  · simp

lemma D_ne_zero : D ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.constantCoeff) h
  simp [D] at this

lemma E_of_ne {F : Finset (Fin k)} (hF : F ≠ ∅) : E F = 0 := by
  ext n; simp [E, δ, hF]

lemma E_empty : E (∅ : Finset (Fin k)) = 1 := by
  ext n; cases n <;> simp [E, δ, PowerSeries.coeff_one]

lemma G_rec (β' : Traj k) (F' : Finset (Fin k)) :
    G β' F' = X * (if flips β' ⊆ F' then
      E (F' \ flips β') + ∑ β : Traj k, (if Compat β β' then G β (F' \ flips β') else 0)
      else 0) := by
  ext n
  cases n with
  | zero => simp only [G]; split_ifs <;> simp [g]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    by_cases h : flips β' ⊆ F'
    · simp only [G, g, h, if_true, coeff_mk, map_add, map_sum, E]
      push_cast
      refine congrArg _ (Finset.sum_congr rfl (fun β _ => ?_))
      split_ifs <;> simp
    · simp [G, g, h]

lemma G_eq_zero_of_not_subset {β : Traj k} {F : Finset (Fin k)} (h : ¬ flips β ⊆ F) :
    G β F = 0 := by
  ext n; simp [G, g_eq_zero_of_not_subset h]

lemma G_zero (F : Finset (Fin k)) : G zero F = X * (E F + T F) := by
  rw [G_rec]
  simp [flips_zero, compat_zero_right, T]

lemma G_one (F : Finset (Fin k)) : G one F = X * (E F + G zero F) := by
  rw [G_rec]
  simp [flips_one, compat_one_iff]

lemma T_split [NeZero k] (F : Finset (Fin k)) : T F = G zero F + G one F + A F := by
  unfold T A
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun β : Traj k => flips β = ∅),
    filter_flips_empty, Finset.sum_pair zero_ne_one]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext β; simp [Finset.nonempty_iff_ne_empty]

lemma T_mul_D [NeZero k] (F : Finset (Fin k)) :
    T F * D = A F + E F * (2 * X + X ^ 2) := by
  have h1 := G_zero F
  have h2 := G_one F
  have h3 := T_split F
  unfold D
  linear_combination (1 + X) * h1 + h2 + h3

/-- `A ∅ = 0`: a flipping trajectory cannot have its flips inside `∅`. -/
lemma A_empty : A (∅ : Finset (Fin k)) = 0 := by
  unfold A
  refine Finset.sum_eq_zero (fun β hβ => G_eq_zero_of_not_subset ?_)
  simp only [mem_filter] at hβ
  intro hs
  obtain ⟨t, ht⟩ := hβ.2
  exact absurd (hs ht) (by simp)

/-! ### The degree-bookkeeping predicate -/

/-- `Good S e d` : `S · D^e` is a polynomial of degree at most `d`. -/
def Good (S : PowerSeries ℤ) (e d : ℕ) : Prop :=
  ∃ p : Polynomial ℤ, p.natDegree ≤ d ∧ S * D ^ e = (p : PowerSeries ℤ)

lemma Good.zero (e d : ℕ) : Good 0 e d := ⟨0, by simp, by simp⟩

lemma Good.add {S S' : PowerSeries ℤ} {e d : ℕ} (h : Good S e d) (h' : Good S' e d) :
    Good (S + S') e d := by
  obtain ⟨p, hp, hS⟩ := h
  obtain ⟨p', hp', hS'⟩ := h'
  refine ⟨p + p', (Polynomial.natDegree_add_le _ _).trans (max_le hp hp'), ?_⟩
  rw [add_mul, hS, hS', Polynomial.coe_add]

lemma Good.sum {ι : Type*} (s : Finset ι) (S : ι → PowerSeries ℤ) {e d : ℕ}
    (h : ∀ i ∈ s, Good (S i) e d) : Good (∑ i ∈ s, S i) e d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.zero e d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma Good.mono {S : PowerSeries ℤ} {e d d' : ℕ} (h : Good S e d) (hd : d ≤ d') : Good S e d' := by
  obtain ⟨p, hp, hS⟩ := h
  exact ⟨p, hp.trans hd, hS⟩

lemma Good.lift {S : PowerSeries ℤ} {e d : ℕ} (h : Good S e d) : Good S (e + 1) (d + 2) := by
  obtain ⟨p, hp, hS⟩ := h
  refine ⟨p * Dp, (Polynomial.natDegree_mul_le).trans (add_le_add hp natDegree_Dp_le), ?_⟩
  rw [pow_succ, ← mul_assoc, hS, Polynomial.coe_mul, coe_Dp]

lemma Good.lift_many {S : PowerSeries ℤ} {e d : ℕ} (h : Good S e d) (j : ℕ) :
    Good S (e + j) (d + 2 * j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have := ih.lift
    rw [show e + (j + 1) = e + j + 1 by ring, show d + 2 * (j + 1) = d + 2 * j + 2 by ring]
    exact this

lemma Good.X_mul {S : PowerSeries ℤ} {e d : ℕ} (h : Good S e d) : Good (X * S) e (d + 1) := by
  obtain ⟨p, hp, hS⟩ := h
  refine ⟨Polynomial.X * p, ?_, ?_⟩
  · refine (Polynomial.natDegree_mul_le).trans ?_
    have := Polynomial.natDegree_X_le (R := ℤ)
    omega
  · rw [mul_assoc, hS, Polynomial.coe_mul, Polynomial.coe_X]

lemma Good.div {S S' : PowerSeries ℤ} {e d : ℕ} (h : Good S e d) (hS' : S' * D = S) :
    Good S' (e + 1) d := by
  obtain ⟨p, hp, hS⟩ := h
  refine ⟨p, hp, ?_⟩
  rw [pow_succ', ← mul_assoc, hS', hS]

/-! ### The main induction -/

/-- If `|F| < 2`, every flipping trajectory has vanishing series at `F`. -/
lemma G_eq_zero_of_card_lt {β : Traj k} (hβ : (flips β).Nonempty) {F : Finset (Fin k)}
    (hF : F.card < 2) : G β F = 0 := by
  refine G_eq_zero_of_not_subset (fun hs => ?_)
  have := Finset.card_le_card hs
  have := two_le_card_flips hβ
  omega

lemma A_eq_zero_of_card_lt {F : Finset (Fin k)} (hF : F.card < 2) : A F = 0 := by
  unfold A
  exact Finset.sum_eq_zero (fun β hβ => G_eq_zero_of_card_lt (mem_filter.1 hβ).2 hF)

/-- The decomposition of `G β' F'` for a flipping `β'` with `flips β' ⊆ F'`. -/
lemma G_active [NeZero k] {β' : Traj k} (hβ' : (flips β').Nonempty) {F' : Finset (Fin k)}
    (hs : flips β' ⊆ F') :
    G β' F' = X * (E (F' \ flips β') + G zero (F' \ flips β') +
      ∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty),
        (if Compat β β' then G β (F' \ flips β') else 0)) := by
  rw [G_rec, if_pos hs]
  congr 1
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun β : Traj k => flips β = ∅),
    filter_flips_empty, Finset.sum_pair zero_ne_one, if_pos (compat_zero_left β'),
    if_neg (not_compat_one_of_nonempty hβ'), add_zero]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext β; simp [Finset.nonempty_iff_ne_empty]

theorem good_active [NeZero k] :
    ∀ (c : ℕ) (F' : Finset (Fin k)), F'.card = c → ∀ β' : Traj k, (flips β').Nonempty →
      2 ≤ F'.card → Good (G β' F') (F'.card / 2) (3 * (F'.card / 2) - 2) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro F' hc β' hβ' h2
  by_cases hs : flips β' ⊆ F'
  swap
  · rw [G_eq_zero_of_not_subset hs]; exact Good.zero _ _
  set F := F' \ flips β' with hFdef
  have hcardF : F.card + (flips β').card = F'.card := by
    rw [hFdef, Finset.card_sdiff_of_subset hs]
    have := Finset.card_le_card hs
    omega
  have h2β := two_le_card_flips hβ'
  set h' := F'.card / 2 with hh'
  have hh'1 : 1 ≤ h' := by omega
  rw [G_active hβ' hs]
  by_cases hF0 : F = ∅
  · -- `F = ∅`: the series equals `z / D`.
    have hA : ∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty),
        (if Compat β β' then G β F else 0) = 0 := by
      refine Finset.sum_eq_zero (fun β hβ => ?_)
      rw [hF0, G_eq_zero_of_card_lt (mem_filter.1 hβ).2 (by simp)]
      simp
    rw [← hFdef, hA, add_zero, hF0, E_empty]
    have hT := T_mul_D (k := k) ∅
    rw [A_empty, E_empty] at hT
    have hz := G_zero (k := k) ∅
    rw [E_empty] at hz
    have hgood : Good (X * (1 + G zero (∅ : Finset (Fin k)))) 1 1 := by
      refine ⟨Polynomial.X, Polynomial.natDegree_X_le, ?_⟩
      rw [Polynomial.coe_X, pow_one]
      unfold D at hT ⊢
      linear_combination X * (1 - X - X ^ 2) * hz + X ^ 2 * hT
    have := hgood.lift_many (h' - 1)
    rw [show 1 + (h' - 1) = h' by omega] at this
    exact this.mono (by omega)
  · -- `F ≠ ∅`.
    have hE : E F = 0 := E_of_ne hF0
    rw [← hFdef, hE, zero_add]
    by_cases hF2 : F.card < 2
    · have hAF := A_eq_zero_of_card_lt hF2
      have hT := T_mul_D F
      rw [hAF, hE, zero_mul, add_zero] at hT
      have hT0 : T F = 0 := by
        rcases mul_eq_zero.1 hT with h | h
        · exact h
        · exact absurd h D_ne_zero
      have hz := G_zero F
      rw [hE, hT0, zero_add, mul_zero] at hz
      have hA : ∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty),
          (if Compat β β' then G β F else 0) = 0 := by
        refine Finset.sum_eq_zero (fun β hβ => ?_)
        rw [G_eq_zero_of_card_lt (mem_filter.1 hβ).2 hF2]
        simp
      rw [hz, hA]
      simpa using Good.zero h' (3 * h' - 2)
    · push_neg at hF2
      set h := F.card / 2 with hh
      have hlt : F.card < c := by omega
      have hh1 : 1 ≤ h := by omega
      have hhh : h + 1 ≤ h' := by omega
      have IH : ∀ β : Traj k, (flips β).Nonempty → Good (G β F) h (3 * h - 2) :=
        fun β hβ => ih F.card hlt F rfl β hβ hF2
      have hAgood : Good (A F) h (3 * h - 2) :=
        Good.sum _ _ (fun β hβ => IH β (mem_filter.1 hβ).2)
      have hT := T_mul_D F
      rw [hE, zero_mul, add_zero] at hT
      have hTgood : Good (T F) (h + 1) (3 * h - 2) := hAgood.div hT
      have hz := G_zero F
      rw [hE, zero_add] at hz
      have hzgood : Good (G zero F) (h + 1) (3 * h) := by
        rw [hz]; exact hTgood.X_mul.mono (by omega)
      have hsum : Good (∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty),
          (if Compat β β' then G β F else 0)) (h + 1) (3 * h) := by
        refine Good.sum _ _ (fun β hβ => ?_)
        split_ifs
        · exact (IH β (mem_filter.1 hβ).2).lift.mono (by omega)
        · exact Good.zero _ _
      have hS := (hzgood.add hsum).X_mul
      have := hS.lift_many (h' - (h + 1))
      rw [show h + 1 + (h' - (h + 1)) = h' by omega] at this
      exact this.mono (by omega)

/-- The total series at `F = univ` satisfies `T · D^(⌊k/2⌋+1) ∈ ℤ[z]` with degree at most
`3⌊k/2⌋ - 2`, for every `k ≥ 2`. -/
theorem good_total (hk : 2 ≤ k) :
    Good (T (univ : Finset (Fin k))) (k / 2 + 1) (3 * (k / 2) - 2) := by
  haveI : NeZero k := ⟨by omega⟩
  have hcard : (univ : Finset (Fin k)).card = k := by simp
  have hA : Good (A (univ : Finset (Fin k))) (k / 2) (3 * (k / 2) - 2) := by
    refine Good.sum _ _ (fun β hβ => ?_)
    have := good_active k univ hcard β (mem_filter.1 hβ).2 (by omega)
    rwa [hcard] at this
  have hT := T_mul_D (univ : Finset (Fin k))
  rw [E_of_ne (by simp [Finset.univ_eq_empty_iff]), zero_mul, add_zero] at hT
  exact hA.div hT

end APEX.PXP
