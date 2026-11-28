/-
# Temporal trajectories for closed walks on the Fibonacci cube

A closed walk of length `k` on the Fibonacci cube `Γₙ` (the PXP configuration graph) is
recorded site by site: site `j` carries a cyclic *temporal trajectory* `β : Fin k → Bool`
(its occupation at times `0, …, k-1`).  The *flip set* of `β` is the set of times `t` at which
the bit changes between `t` and `t+1 (mod k)`.

Main facts proved here:
* `card_flips_even`  : every flip set has even cardinality;
* `two_le_card_flips` : a trajectory with at least one flip has at least two;
* `flips_eq_empty_iff` : no flips iff the trajectory is constant (`zero` or `one`).
-/
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

namespace APEX.PXP

open Finset

variable {k : ℕ}

/-- A cyclic temporal trajectory of one site. -/
abbrev Traj (k : ℕ) := Fin k → Bool

/-- The flip set `D(β) = {t | β (t+1) ≠ β t}` (time is cyclic via `finRotate`). -/
def flips (β : Traj k) : Finset (Fin k) := univ.filter (fun t => β (finRotate k t) ≠ β t)

lemma mem_flips {β : Traj k} {t : Fin k} : t ∈ flips β ↔ β (finRotate k t) ≠ β t := by
  simp [flips]

/-- The all-empty trajectory. -/
def zero : Traj k := fun _ => false

/-- The all-occupied trajectory. -/
def one : Traj k := fun _ => true

/-- Spatial blockade: two neighbouring sites are never simultaneously occupied. -/
def Compat (β γ : Traj k) : Prop := ∀ t, ¬ (β t = true ∧ γ t = true)

instance : DecidableRel (Compat (k := k)) := fun _ _ => by unfold Compat; infer_instance

lemma card_flips_even (β : Traj k) : Even (flips β).card := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  have h : ∀ t, (if β (finRotate k t) ≠ β t then (1 : ZMod 2) else 0)
      = (if β (finRotate k t) = true then 1 else 0) + (if β t = true then 1 else 0) := by
    intro t
    cases β (finRotate k t) <;> cases β t <;> decide
  rw [flips, natCast_card_filter, Finset.sum_congr rfl (fun t _ => h t), Finset.sum_add_distrib,
    Equiv.sum_comp (finRotate k) (fun t => if β t = true then (1 : ZMod 2) else 0), ← two_mul]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_mul]

lemma two_le_card_flips {β : Traj k} (h : (flips β).Nonempty) : 2 ≤ (flips β).card := by
  obtain ⟨r, hr⟩ := card_flips_even β
  have := h.card_pos
  omega

lemma const_of_flips_eq_empty {β : Traj k} (h : flips β = ∅) (t s : Fin k) : β t = β s := by
  have hrot : ∀ t, β (finRotate k t) = β t := by
    intro t
    by_contra hc
    have : t ∈ flips β := mem_flips.2 hc
    simp [h] at this
  cases k with
  | zero => exact t.elim0
  | succ n =>
    have hv : ∀ j : ℕ, ∀ hj : j < n + 1, β ⟨j, hj⟩ = β 0 := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have e := finRotate_of_lt (n := n) (k := j) (by omega)
        rw [← ih (by omega), ← hrot ⟨j, by omega⟩, e]
    have key : ∀ u : Fin (n + 1), β u = β 0 := fun u => hv u.val u.isLt
    rw [key t, key s]

lemma flips_eq_empty_iff {β : Traj k} : flips β = ∅ ↔ β = zero ∨ β = one := by
  constructor
  · intro h
    cases k with
    | zero => left; funext t; exact t.elim0
    | succ n =>
      cases h0 : β 0
      · left; funext t; rw [const_of_flips_eq_empty h t 0, h0]; rfl
      · right; funext t; rw [const_of_flips_eq_empty h t 0, h0]; rfl
  · rintro (rfl | rfl) <;> simp [flips, zero, one]

lemma flips_zero : flips (zero : Traj k) = ∅ := flips_eq_empty_iff.2 (Or.inl rfl)

lemma flips_one : flips (one : Traj k) = ∅ := flips_eq_empty_iff.2 (Or.inr rfl)

lemma zero_ne_one [NeZero k] : (zero : Traj k) ≠ one := by
  intro h
  have := congrFun h 0
  simp [zero, one] at this

lemma compat_zero_left (β : Traj k) : Compat zero β := by
  intro t; simp [zero]

lemma compat_zero_right (β : Traj k) : Compat β zero := by
  intro t; simp [zero]

lemma compat_one_iff (β : Traj k) : Compat β one ↔ β = zero := by
  constructor
  · intro h; funext t; have := h t; simp [one] at this; simpa [zero] using this
  · rintro rfl; intro t; simp [zero]

lemma not_compat_one_of_nonempty {β : Traj k} (h : (flips β).Nonempty) : ¬ Compat one β := by
  intro hc
  have hz : β = zero := by
    funext t; have := hc t; simp [one] at this; simpa [zero] using this
  rw [hz, flips_zero] at h
  simp at h

/-- The set of trajectories with no flips is exactly `{zero, one}`. -/
lemma filter_flips_empty [NeZero k] :
    (univ.filter (fun β : Traj k => flips β = ∅)) = {zero, one} := by
  ext β
  simp [flips_eq_empty_iff]

end APEX.PXP
