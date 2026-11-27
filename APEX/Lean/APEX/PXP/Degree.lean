/-
# The numerator degree is exactly `3m - 2`

**Theorem (`pxp_numerator_natDegree`).**  For every `m ≥ 1`, the numerator `P_m` of
`∑ₙ Tr Aₙ^{2m} zⁿ = P_m / (1 - z - z²)^(m+1)` has `natDegree P_m = 3m - 2`.

The top coefficient is `(-1)^(m-1) c_m`, where `c_m ≥ 1` counts chains of two-flip
trajectories on adjacent sites; positivity is witnessed by the chain of single-time pulses
`β_j = 1_{t = 2j-1}`.  We only prove `(-1)^(m-1) · coeff ≥ 1`.
-/
import APEX.PXP.Residue

namespace APEX.PXP

open Finset PowerSeries

variable {k : ℕ}

/-! ### Top-coefficient bookkeeping -/

/-- `GoodT S e d c` : `S · D^e = p`, `deg p ≤ d`, and the coefficient of `z^d` in `p` is `c`. -/
def GoodT (S : PowerSeries ℤ) (e d : ℕ) (c : ℤ) : Prop :=
  ∃ p : Polynomial ℤ, p.natDegree ≤ d ∧ S * D ^ e = (p : PowerSeries ℤ) ∧ p.coeff d = c

lemma GoodT.zero (e d : ℕ) : GoodT 0 e d 0 := ⟨0, by simp, by simp, by simp⟩

lemma GoodT.add {S S' : PowerSeries ℤ} {e d : ℕ} {c c' : ℤ} (h : GoodT S e d c)
    (h' : GoodT S' e d c') : GoodT (S + S') e d (c + c') := by
  obtain ⟨p, hp, hS, hc⟩ := h
  obtain ⟨p', hp', hS', hc'⟩ := h'
  refine ⟨p + p', (Polynomial.natDegree_add_le _ _).trans (max_le hp hp'), ?_, ?_⟩
  · rw [add_mul, hS, hS', Polynomial.coe_add]
  · rw [Polynomial.coeff_add, hc, hc']

lemma GoodT.sum {ι : Type*} (s : Finset ι) (S : ι → PowerSeries ℤ) (c : ι → ℤ) {e d : ℕ}
    (h : ∀ i ∈ s, GoodT (S i) e d (c i)) : GoodT (∑ i ∈ s, S i) e d (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GoodT.zero e d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma coeff_two_Dp : Dp.coeff 2 = -1 := by
  simp [Dp, Polynomial.coeff_one, Polynomial.coeff_X]

lemma GoodT.lift {S : PowerSeries ℤ} {e d : ℕ} {c : ℤ} (h : GoodT S e d c) :
    GoodT S (e + 1) (d + 2) (-c) := by
  obtain ⟨p, hp, hS, hc⟩ := h
  refine ⟨p * Dp, (Polynomial.natDegree_mul_le).trans (add_le_add hp natDegree_Dp_le), ?_, ?_⟩
  · rw [pow_succ, ← mul_assoc, hS, Polynomial.coe_mul, coe_Dp]
  · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hp natDegree_Dp_le, hc, coeff_two_Dp]
    ring

lemma GoodT.X_mul {S : PowerSeries ℤ} {e d : ℕ} {c : ℤ} (h : GoodT S e d c) :
    GoodT (X * S) e (d + 1) c := by
  obtain ⟨p, hp, hS, hc⟩ := h
  refine ⟨Polynomial.X * p, ?_, ?_, ?_⟩
  · refine (Polynomial.natDegree_mul_le).trans ?_
    have := Polynomial.natDegree_X_le (R := ℤ)
    omega
  · rw [mul_assoc, hS, Polynomial.coe_mul, Polynomial.coe_X]
  · rw [Polynomial.coeff_X_mul, hc]

lemma GoodT.div {S S' : PowerSeries ℤ} {e d : ℕ} {c : ℤ} (h : GoodT S e d c)
    (hS' : S' * D = S) : GoodT S' (e + 1) d c := by
  obtain ⟨p, hp, hS, hc⟩ := h
  exact ⟨p, hp, by rw [pow_succ', ← mul_assoc, hS', hS], hc⟩

lemma GoodT.of_good_lt {S : PowerSeries ℤ} {e d d' : ℕ} (h : Good S e d) (hd : d < d') :
    GoodT S e d' 0 := by
  obtain ⟨p, hp, hS⟩ := h
  exact ⟨p, hp.trans hd.le, hS, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)⟩

lemma GoodT.toGood {S : PowerSeries ℤ} {e d : ℕ} {c : ℤ} (h : GoodT S e d c) : Good S e d := by
  obtain ⟨p, hp, hS, -⟩ := h
  exact ⟨p, hp, hS⟩

/-! ### The pulse chain -/

/-- Pulse trajectory occupied only at time `2j - 1`, as an interval trajectory. -/
def pa (j : ℕ) (hj : 1 ≤ j) (hj' : 2 * j ≤ k) : Fin k := ⟨2 * j - 2, by omega⟩
def pb (j : ℕ) (hj : 1 ≤ j) (hj' : 2 * j ≤ k) : Fin k := ⟨2 * j - 1, by omega⟩

/-- Times `< 2j`. -/
def seg (j : ℕ) : Finset (Fin k) := univ.filter (fun t => t.val < 2 * j)

lemma card_seg {j : ℕ} (hj : 2 * j ≤ k) : (seg (k := k) j).card = 2 * j := by
  unfold seg
  have := Fin.card_filter_val_lt (n := k) (m := 2 * j)
  rw [this]; omega

lemma pa_lt_pb {j : ℕ} (hj : 1 ≤ j) (hj' : 2 * j ≤ k) : pa j hj hj' < pb j hj hj' := by
  rw [Fin.lt_def]; simp [pa, pb]; omega

lemma flips_pulse {j : ℕ} (hj : 1 ≤ j) (hj' : 2 * j ≤ k) :
    flips (ival (pa j hj hj') (pb j hj hj')) = {pa j hj hj', pb j hj hj'} :=
  flips_ival (pa_lt_pb hj hj')

lemma flips_pulse_subset {j : ℕ} (hj : 1 ≤ j) (hj' : 2 * j ≤ k) :
    flips (ival (pa j hj hj') (pb j hj hj')) ⊆ seg j := by
  rw [flips_pulse]
  intro t ht
  simp only [mem_insert, mem_singleton] at ht
  simp only [seg, mem_filter, mem_univ, true_and]
  rcases ht with rfl | rfl <;> simp [pa, pb] <;> omega

lemma seg_sdiff_pulse {j : ℕ} (hj : 1 ≤ j) (hj' : 2 * j ≤ k) :
    seg j \ flips (ival (pa j hj hj') (pb j hj hj')) = seg (j - 1) := by
  rw [flips_pulse]
  ext t
  simp only [seg, mem_sdiff, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
    Fin.ext_iff, pa, pb]
  omega

lemma pulse_nonempty {j : ℕ} (hj : 1 ≤ j) (hj' : 2 * j ≤ k) :
    (flips (ival (pa j hj hj') (pb j hj hj'))).Nonempty := by
  rw [flips_pulse]; simp

lemma compat_pulse {j : ℕ} (hj : 2 ≤ j) (hj' : 2 * j ≤ k) :
    Compat (ival (pa (j - 1) (by omega) (by omega)) (pb (j - 1) (by omega) (by omega)))
      (ival (pa j (by omega) hj') (pb j (by omega) hj')) := by
  intro t ht
  simp only [ival, decide_eq_true_eq, Fin.lt_def, Fin.le_def, pa, pb] at ht
  omega

/-! ### The main induction for the top coefficient -/

/-- Special pairs: the pulse chain. -/
def Special (β : Traj k) (F : Finset (Fin k)) : Prop :=
  ∃ (j : ℕ) (hj : 1 ≤ j) (hj' : 2 * j ≤ k), F = seg j ∧ β = ival (pa j hj hj') (pb j hj hj')

lemma sign_step (h : ℕ) (hh : 1 ≤ h) (x : ℤ) : (-1 : ℤ) ^ h * (-x) = (-1) ^ (h - 1) * x := by
  obtain ⟨r, rfl⟩ : ∃ r, h = r + 1 := ⟨h - 1, by omega⟩
  simp [pow_succ]

theorem goodT_active [NeZero k] :
    ∀ (c : ℕ) (F' : Finset (Fin k)), F'.card = c → ∀ β' : Traj k, (flips β').Nonempty →
      2 ≤ F'.card → ∃ cc : ℤ, GoodT (G β' F') (F'.card / 2) (3 * (F'.card / 2) - 2) cc ∧
        0 ≤ (-1) ^ (F'.card / 2 - 1) * cc ∧ (Special β' F' → 1 ≤ (-1) ^ (F'.card / 2 - 1) * cc) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro F' hc β' hβ' h2
  have hgood := good_active c F' hc β' hβ' h2
  by_cases hs : flips β' ⊆ F'
  swap
  · refine ⟨0, ?_, by simp, ?_⟩
    · rw [G_eq_zero_of_not_subset hs]; exact GoodT.zero _ _
    · rintro ⟨j, hj, hj', rfl, rfl⟩
      exact absurd (flips_pulse_subset hj hj') hs
  set F := F' \ flips β' with hFdef
  have hcardF : F.card + (flips β').card = F'.card := by
    rw [hFdef, Finset.card_sdiff_of_subset hs]
    have := Finset.card_le_card hs
    omega
  have h2β := two_le_card_flips hβ'
  obtain ⟨rβ, hrβ⟩ := card_flips_even β'
  set h' := F'.card / 2 with hh'
  have hh'1 : 1 ≤ h' := by omega
  -- if the bound is not attained at this level, the coefficient is `0`
  have hspec2 : Special β' F' → (flips β').card = 2 ∧ F.card = F'.card - 2 := by
    rintro ⟨j, hj, hj', hF', hβ⟩
    have : (flips β').card = 2 := by rw [hβ, flips_pulse]; simp [Finset.card_pair (pa_lt_pb hj hj').ne]
    exact ⟨this, by omega⟩
  by_cases hF0 : F = ∅
  · -- `G β' F' = z / D`
    have hzD : G β' F' * D = X := by
      rw [G_active hβ' hs]
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
      unfold D at hT ⊢
      linear_combination X * (1 - X - X ^ 2) * hz + X ^ 2 * hT
    by_cases hh1 : h' = 1
    · refine ⟨1, ?_, by simp [hh1], fun _ => by simp [hh1]⟩
      rw [hh1]
      exact ⟨Polynomial.X, Polynomial.natDegree_X_le, by rw [pow_one, hzD, Polynomial.coe_X],
        by simp⟩
    · refine ⟨0, ?_, by simp, ?_⟩
      · have hg : Good (G β' F') 1 1 :=
          ⟨Polynomial.X, Polynomial.natDegree_X_le, by rw [pow_one, hzD, Polynomial.coe_X]⟩
        have := hg.lift_many (h' - 1)
        rw [show 1 + (h' - 1) = h' by omega] at this
        exact GoodT.of_good_lt this (by omega)
      · intro hsp
        have := hspec2 hsp
        have : F.card = 0 := by rw [hF0]; rfl
        omega
  · by_cases hF2 : F.card < 2
    · refine ⟨0, ?_, by simp, ?_⟩
      · -- the series vanishes
        have hE : E F = 0 := E_of_ne hF0
        have hAF := A_eq_zero_of_card_lt hF2
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
        rw [G_active hβ' hs, ← hFdef, hE, hz, hA]
        simpa using GoodT.zero h' (3 * h' - 2)
      · rintro ⟨j, hj, hj', hF', hβ⟩
        have hFs : F = seg (j - 1) := by rw [hFdef, hF', hβ, seg_sdiff_pulse]
        have : F.card = 2 * (j - 1) := by rw [hFs, card_seg (by omega)]
        rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · exact (hF0 (by rw [hFs]; ext t; simp [seg]; omega)).elim
        · omega
    · push_neg at hF2
      set h := F.card / 2 with hh
      have hlt : F.card < c := by omega
      have hh1 : 1 ≤ h := by omega
      have hhh : h + 1 ≤ h' := by omega
      have IH : ∀ β : Traj k, (flips β).Nonempty → ∃ cc : ℤ, GoodT (G β F) h (3 * h - 2) cc ∧
          0 ≤ (-1) ^ (h - 1) * cc ∧ (Special β F → 1 ≤ (-1) ^ (h - 1) * cc) :=
        fun β hβ => ih F.card hlt F rfl β hβ hF2
      choose! cf hcf using IH
      have hE : E F = 0 := E_of_ne hF0
      have hT := T_mul_D F
      rw [hE, zero_mul, add_zero] at hT
      have hAgood : Good (A F) h (3 * h - 2) :=
        Good.sum _ _ (fun β hβ => (hcf β (mem_filter.1 hβ).2).1.toGood)
      have hTgood : Good (T F) (h + 1) (3 * h - 2) := hAgood.div hT
      have hz := G_zero F
      rw [hE, zero_add] at hz
      have hzT : GoodT (G zero F) (h + 1) (3 * h) 0 := by
        rw [hz]; exact GoodT.of_good_lt hTgood.X_mul (by omega)
      have hsum : GoodT (∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty),
          (if Compat β β' then G β F else 0)) (h + 1) (3 * h)
          (∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty),
            (if Compat β β' then -cf β else 0)) := by
        refine GoodT.sum _ _ _ (fun β hβ => ?_)
        split_ifs
        · have := (hcf β (mem_filter.1 hβ).2).1.lift
          rwa [show 3 * h - 2 + 2 = 3 * h by omega] at this
        · exact GoodT.zero _ _
      have hG' : GoodT (G β' F') (h + 1) (3 * h + 1)
          (0 + ∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty),
            (if Compat β β' then -cf β else 0)) := by
        rw [G_active hβ' hs, ← hFdef, hE, zero_add]
        exact (hzT.add hsum).X_mul
      by_cases hhe : h' = h + 1
      · refine ⟨0 + ∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty),
            (if Compat β β' then -cf β else 0), ?_, ?_, ?_⟩
        · rw [hhe, show 3 * (h + 1) - 2 = 3 * h + 1 by omega]; exact hG'
        · rw [hhe, Nat.add_sub_cancel, zero_add, Finset.mul_sum]
          refine Finset.sum_nonneg (fun β hβ => ?_)
          split_ifs
          · rw [sign_step h hh1]; exact (hcf β (mem_filter.1 hβ).2).2.1
          · simp
        · rintro ⟨j, hj, hj', hF', hβ⟩
          have hFs : F = seg (j - 1) := by rw [hFdef, hF', hβ, seg_sdiff_pulse]
          have hj2 : 2 ≤ j := by
            by_contra hcon
            exact hF0 (by rw [hFs]; ext t; simp [seg]; omega)
          rw [hhe, Nat.add_sub_cancel, zero_add, Finset.mul_sum]
          set β'' := ival (pa (j - 1) (k := k) (by omega) (by omega)) (pb (j - 1) (by omega) (by omega))
          have hβ''n : (flips β'').Nonempty := pulse_nonempty (by omega) (by omega)
          have hmem : β'' ∈ univ.filter (fun β : Traj k => (flips β).Nonempty) := by
            simp [hβ''n]
          have hcomp : Compat β'' β' := by rw [hβ]; exact compat_pulse hj2 hj'
          have hspec : Special β'' F := ⟨j - 1, by omega, by omega, hFs, rfl⟩
          have hterm : 1 ≤ (-1 : ℤ) ^ h * (if Compat β'' β' then -cf β'' else 0) := by
            rw [if_pos hcomp, sign_step h hh1]; exact (hcf β'' hβ''n).2.2 hspec
          refine hterm.trans (Finset.single_le_sum (f := fun β => (-1 : ℤ) ^ h *
            (if Compat β β' then -cf β else 0)) (fun β hβ => ?_) hmem)
          split_ifs
          · rw [sign_step h hh1]; exact (hcf β (mem_filter.1 hβ).2).2.1
          · simp
      · refine ⟨0, ?_, by simp, ?_⟩
        · have := hG'.toGood.lift_many (h' - (h + 1))
          rw [show h + 1 + (h' - (h + 1)) = h' by omega] at this
          exact GoodT.of_good_lt this (by omega)
        · intro hsp; have := hspec2 hsp; omega

/-- **Exact numerator degree.** -/
theorem pxp_numerator_natDegree (m : ℕ) (hm : 1 ≤ m) (P : Polynomial ℤ)
    (hP : PowerSeries.mk (fun n => M (2 * m) n) * (1 - X - X ^ 2) ^ (m + 1) = (P : PowerSeries ℤ)) :
    P.natDegree = 3 * m - 2 ∧ 1 ≤ (-1 : ℤ) ^ (m - 1) * P.coeff (3 * m - 2) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hcard : (univ : Finset (Fin (2 * m))).card = 2 * m := by simp
  have hk : 2 * m / 2 = m := by omega
  have IH : ∀ β : Traj (2 * m), (flips β).Nonempty → ∃ cc : ℤ,
      GoodT (G β univ) m (3 * m - 2) cc ∧ 0 ≤ (-1) ^ (m - 1) * cc ∧
        (Special β univ → 1 ≤ (-1) ^ (m - 1) * cc) := by
    intro β hβ
    have := goodT_active (2 * m) univ hcard β hβ (by omega)
    rwa [hcard, hk] at this
  choose! cf hcf using IH
  have hA : GoodT (A (univ : Finset (Fin (2 * m)))) m (3 * m - 2)
      (∑ β ∈ univ.filter (fun β : Traj (2 * m) => (flips β).Nonempty), cf β) :=
    GoodT.sum _ _ _ (fun β hβ => (hcf β (mem_filter.1 hβ).2).1)
  have hT := T_mul_D (univ : Finset (Fin (2 * m)))
  rw [E_of_ne (by simp [Finset.univ_eq_empty_iff]), zero_mul, add_zero] at hT
  obtain ⟨P', hP', hPe, hc⟩ := hA.div hT
  have hPP : P = P' := by
    have h1 := hP
    rw [series_M_eq_T] at h1
    unfold D at hPe
    exact Polynomial.coe_inj.1 (h1.symm.trans hPe)
  subst hPP
  -- the special pulse chain gives a term `≥ 1`, all others are `≥ 0`
  set β0 := ival (pa m (k := 2 * m) hm (by omega)) (pb m hm (by omega))
  have hβ0 : (flips β0).Nonempty := pulse_nonempty hm (by omega)
  have hseg : (seg m : Finset (Fin (2 * m))) = univ := by
    ext t; simp [seg]
  have hspec : Special β0 univ := ⟨m, hm, by omega, hseg.symm, rfl⟩
  have hmem : β0 ∈ univ.filter (fun β : Traj (2 * m) => (flips β).Nonempty) := by simp [hβ0]
  have hpos : 1 ≤ (-1 : ℤ) ^ (m - 1) * P.coeff (3 * m - 2) := by
    rw [hc, Finset.mul_sum]
    exact ((hcf β0 hβ0).2.2 hspec).trans (Finset.single_le_sum
      (f := fun β => (-1 : ℤ) ^ (m - 1) * cf β)
      (fun β hβ => (hcf β (mem_filter.1 hβ).2).2.1) hmem)
  refine ⟨Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hP' ?_, hpos⟩
  intro h0
  rw [h0, mul_zero] at hpos
  omega

end APEX.PXP
