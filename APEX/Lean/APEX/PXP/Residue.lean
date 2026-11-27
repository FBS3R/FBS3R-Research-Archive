/-
# Sharpness of the denominator: the residue of `P_m` modulo `1 - z - z²`

**Theorem (`pxp_moment_residue`).**  The numerator of `pxp_moment_rational` satisfies
`P_m ≡ (2m)! · z^(2m-1)  (mod 1 - z - z²)` in `ℤ[z]`.

**Corollary (`pxp_denominator_sharp`).**  `1 - z - z²` does not divide `P_m`; hence the
reduced denominator of `∑ₙ Tr Aₙ^{2m} zⁿ` is exactly `(1 - z - z²)^(m+1)`.

Combinatorial content: modulo `D`, only arrays in which every active site flips exactly twice
and consecutive active sites are separated survive; they are counted by `(2m)!`.
-/
import APEX.PXP.Main
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset

namespace APEX.PXP

open Finset PowerSeries

variable {k : ℕ}

/-! ### Trajectories with exactly two flips -/

/-- Pointwise negation of a trajectory. -/
def neg (β : Traj k) : Traj k := fun t => !β t

lemma flips_neg (β : Traj k) : flips (neg β) = flips β := by
  ext t; simp only [mem_flips, neg]; cases β (finRotate k t) <;> cases β t <;> simp

lemma neg_ne [NeZero k] (β : Traj k) : neg β ≠ β := by
  intro h
  have := congrFun h 0
  simp [neg] at this

lemma eq_or_eq_neg_of_flips_eq {β γ : Traj k} (h : flips β = flips γ) : γ = β ∨ γ = neg β := by
  let δ : Traj k := fun t => xor (β t) (γ t)
  have hδ : flips δ = ∅ := by
    ext t
    simp only [notMem_empty, iff_false]
    intro ht
    rw [mem_flips] at ht
    have hb : t ∈ flips β ↔ t ∈ flips γ := by rw [h]
    simp only [mem_flips] at hb
    simp only [δ] at ht
    cases h1 : β (finRotate k t) <;> cases h2 : β t <;> cases h3 : γ (finRotate k t) <;>
      cases h4 : γ t <;> simp_all
  rcases flips_eq_empty_iff.1 hδ with h0 | h1
  · left; funext t
    have := congrFun h0 t
    simp only [δ, zero] at this
    cases hb : β t <;> cases hg : γ t <;> simp_all
  · right; funext t
    have := congrFun h1 t
    simp only [δ, one] at this
    cases hb : β t <;> cases hg : γ t <;> simp_all [neg]

/-- The "interval" trajectory, occupied exactly at times `t` with `a < t ≤ b`. -/
def ival (a b : Fin k) : Traj k := fun t => decide (a < t ∧ t ≤ b)

lemma flips_ival {a b : Fin k} (hab : a < b) : flips (ival a b) = {a, b} := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := b.isLt; omega⟩
  ext t
  rw [mem_flips, mem_insert, mem_singleton]
  simp only [ival, ne_eq, decide_eq_decide, Fin.lt_def, Fin.le_def, Fin.ext_iff]
  rw [coe_finRotate]
  have := hab
  rw [Fin.lt_def] at this
  have hb := b.isLt
  have ht := t.isLt
  split_ifs with hl
  · have : (t : ℕ) = n := by rw [hl]; simp
    omega
  · have : (t : ℕ) ≠ n := fun e => hl (Fin.ext (by simp [e]))
    omega

lemma card_fiber_two [NeZero k] {S : Finset (Fin k)} (hS : S.card = 2) :
    (univ.filter (fun β : Traj k => flips β = S)).card = 2 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hS
  clear hS
  wlog hlt : a < b generalizing a b
  · have := this b a hab.symm (lt_of_le_of_ne (not_lt.1 hlt) hab.symm)
    rwa [Finset.pair_comm] at this
  have hf : univ.filter (fun β : Traj k => flips β = {a, b}) = {ival a b, neg (ival a b)} := by
    ext β
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro h
      rcases eq_or_eq_neg_of_flips_eq ((flips_ival hlt).trans h.symm) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · exact flips_ival hlt
      · rw [flips_neg]; exact flips_ival hlt
  rw [hf, Finset.card_pair (neg_ne _).symm]

/-- The number of trajectories whose two flips lie in `F` is `|F|(|F|-1)`. -/
lemma card_two_flips_in [NeZero k] (F : Finset (Fin k)) :
    (univ.filter (fun β : Traj k => (flips β).card = 2 ∧ flips β ⊆ F)).card =
      F.card * (F.card - 1) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := flips) (t := F.powersetCard 2)]
  · have : ∀ S ∈ F.powersetCard 2,
        ((univ.filter (fun β : Traj k => (flips β).card = 2 ∧ flips β ⊆ F)).filter
          (fun β => flips β = S)).card = 2 := by
      intro S hS
      rw [Finset.mem_powersetCard] at hS
      rw [Finset.filter_filter]
      refine Eq.trans ?_ (card_fiber_two hS.2)
      congr 1
      ext β
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; rw [h]; exact ⟨⟨hS.2, hS.1⟩, rfl⟩
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul,
      Nat.choose_two_right, Nat.div_mul_cancel (Nat.even_mul_pred_self _).two_dvd]
  · intro β hβ
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    rw [Finset.mem_coe, Finset.mem_filter] at hβ
    exact ⟨hβ.2.2, hβ.2.1⟩

/-! ### Residue bookkeeping -/

/-- `GoodR S e d r` : `S · D^e = p` with `deg p ≤ d` and `p ≡ r (mod D)`. -/
def GoodR (S : PowerSeries ℤ) (e d : ℕ) (r : Polynomial ℤ) : Prop :=
  ∃ p q : Polynomial ℤ, p.natDegree ≤ d ∧ S * D ^ e = (p : PowerSeries ℤ) ∧ p = r + Dp * q

lemma GoodR.zero (e d : ℕ) : GoodR 0 e d 0 := ⟨0, 0, by simp, by simp, by simp⟩

lemma GoodR.add {S S' : PowerSeries ℤ} {e d : ℕ} {r r' : Polynomial ℤ} (h : GoodR S e d r)
    (h' : GoodR S' e d r') : GoodR (S + S') e d (r + r') := by
  obtain ⟨p, q, hp, hS, hq⟩ := h
  obtain ⟨p', q', hp', hS', hq'⟩ := h'
  refine ⟨p + p', q + q', (Polynomial.natDegree_add_le _ _).trans (max_le hp hp'), ?_, ?_⟩
  · rw [add_mul, hS, hS', Polynomial.coe_add]
  · rw [hq, hq']; ring

lemma GoodR.sum {ι : Type*} (s : Finset ι) (S : ι → PowerSeries ℤ) (r : ι → Polynomial ℤ)
    {e d : ℕ} (h : ∀ i ∈ s, GoodR (S i) e d (r i)) :
    GoodR (∑ i ∈ s, S i) e d (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GoodR.zero e d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma GoodR.mono {S : PowerSeries ℤ} {e d d' : ℕ} {r : Polynomial ℤ} (h : GoodR S e d r)
    (hd : d ≤ d') : GoodR S e d' r := by
  obtain ⟨p, q, hp, hS, hq⟩ := h
  exact ⟨p, q, hp.trans hd, hS, hq⟩

lemma GoodR.congr {S : PowerSeries ℤ} {e d : ℕ} {r r' : Polynomial ℤ} (h : GoodR S e d r)
    (hr : r = r') : GoodR S e d r' := hr ▸ h

lemma GoodR.lift {S : PowerSeries ℤ} {e d : ℕ} {r : Polynomial ℤ} (h : GoodR S e d r) :
    GoodR S (e + 1) (d + 2) 0 := by
  obtain ⟨p, q, hp, hS, hq⟩ := h
  refine ⟨p * Dp, p, (Polynomial.natDegree_mul_le).trans (add_le_add hp natDegree_Dp_le), ?_, ?_⟩
  · rw [pow_succ, ← mul_assoc, hS, Polynomial.coe_mul, coe_Dp]
  · ring

lemma GoodR.lift_many {S : PowerSeries ℤ} {e d : ℕ} {r : Polynomial ℤ} (h : GoodR S e d r)
    (j : ℕ) (hj : 1 ≤ j) : GoodR S (e + j) (d + 2 * j) 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · simpa using h.lift
    · have := (ih hj').lift
      rw [show e + (j + 1) = e + j + 1 by ring, show d + 2 * (j + 1) = d + 2 * j + 2 by ring]
      exact this

lemma GoodR.X_mul {S : PowerSeries ℤ} {e d : ℕ} {r : Polynomial ℤ} (h : GoodR S e d r) :
    GoodR (X * S) e (d + 1) (Polynomial.X * r) := by
  obtain ⟨p, q, hp, hS, hq⟩ := h
  refine ⟨Polynomial.X * p, Polynomial.X * q, ?_, ?_, ?_⟩
  · refine (Polynomial.natDegree_mul_le).trans ?_
    have := Polynomial.natDegree_X_le (R := ℤ)
    omega
  · rw [mul_assoc, hS, Polynomial.coe_mul, Polynomial.coe_X]
  · rw [hq]; ring

lemma GoodR.div {S S' : PowerSeries ℤ} {e d : ℕ} {r : Polynomial ℤ} (h : GoodR S e d r)
    (hS' : S' * D = S) : GoodR S' (e + 1) d r := by
  obtain ⟨p, q, hp, hS, hq⟩ := h
  exact ⟨p, q, hp, by rw [pow_succ', ← mul_assoc, hS', hS], hq⟩

/-- The predicted residue weight of a flipping trajectory. -/
def N2 (β : Traj k) (F : Finset (Fin k)) : ℤ :=
  if (flips β).card = 2 ∧ flips β ⊆ F ∧ Even F.card then ((F.card - 2).factorial : ℤ) else 0

lemma sum_N2 [NeZero k] (F : Finset (Fin k)) (hF : 2 ≤ F.card) (he : Even F.card) :
    ∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty), N2 β F = (F.card.factorial : ℤ) := by
  unfold N2
  simp only [he, and_true]
  rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul]
  have hfil : (univ.filter (fun β : Traj k => (flips β).Nonempty ∧ ((flips β).card = 2 ∧
      flips β ⊆ F))) = univ.filter (fun β : Traj k => (flips β).card = 2 ∧ flips β ⊆ F) := by
    ext β
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨Finset.card_pos.1 (by omega), h⟩
  rw [hfil, card_two_flips_in]
  obtain ⟨c, hc⟩ : ∃ c, F.card = c + 2 := ⟨F.card - 2, by omega⟩
  rw [hc, show c + 2 - 2 = c by omega, show c + 2 - 1 = c + 1 by omega]
  push_cast
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

theorem goodR_active [NeZero k] :
    ∀ (c : ℕ) (F' : Finset (Fin k)), F'.card = c → ∀ β' : Traj k, (flips β').Nonempty →
      2 ≤ F'.card → GoodR (G β' F') (F'.card / 2) (3 * (F'.card / 2) - 2)
        (Polynomial.C (N2 β' F') * Polynomial.X ^ (2 * (F'.card / 2) - 1)) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro F' hc β' hβ' h2
  by_cases hs : flips β' ⊆ F'
  swap
  · rw [G_eq_zero_of_not_subset hs]
    refine (GoodR.zero _ _).congr ?_
    simp [N2, hs]
  set F := F' \ flips β' with hFdef
  have hcardF : F.card + (flips β').card = F'.card := by
    rw [hFdef, Finset.card_sdiff_of_subset hs]
    have := Finset.card_le_card hs
    omega
  have h2β := two_le_card_flips hβ'
  obtain ⟨rβ, hrβ⟩ := card_flips_even β'
  set h' := F'.card / 2 with hh'
  have hh'1 : 1 ≤ h' := by omega
  rw [G_active hβ' hs]
  by_cases hF0 : F = ∅
  · have hA : ∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty),
        (if Compat β β' then G β F else 0) = 0 := by
      refine Finset.sum_eq_zero (fun β hβ => ?_)
      rw [hF0, G_eq_zero_of_card_lt (mem_filter.1 hβ).2 (by simp)]
      simp
    rw [← hFdef, hA, add_zero, hF0, E_empty]
    have hT := T_mul_D (k := k) ∅
    rw [A_empty, E_empty] at hT
    have hz := G_zero (k := k) ∅
    rw [E_empty] at hz
    have hcard0 : F.card = 0 := by rw [hF0]; rfl
    have hgood : GoodR (X * (1 + G zero (∅ : Finset (Fin k)))) 1 1 Polynomial.X := by
      refine ⟨Polynomial.X, 0, Polynomial.natDegree_X_le, ?_, by simp⟩
      rw [Polynomial.coe_X, pow_one]
      unfold D at hT ⊢
      linear_combination X * (1 - X - X ^ 2) * hz + X ^ 2 * hT
    by_cases hh1 : h' = 1
    · -- exactly two flips: residue `X`, weight `0! = 1`
      have hc2 : (flips β').card = 2 := by omega
      have hF'2 : F'.card = 2 := by omega
      rw [hh1]
      refine hgood.congr ?_
      simp [N2, hc2, hs, hF'2]
    · have := hgood.lift_many (h' - 1) (by omega)
      rw [show 1 + (h' - 1) = h' by omega] at this
      refine (this.mono (by omega)).congr ?_
      have hc2 : (flips β').card ≠ 2 := by omega
      simp [N2, hc2]
  · have hE : E F = 0 := E_of_ne hF0
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
      have hF1 : F.card = 1 := by
        have := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hF0)
        omega
      have hodd : ¬ Even F'.card := by
        rintro ⟨s, hs'⟩
        omega
      rw [add_zero, mul_zero]
      refine (GoodR.zero _ _).congr ?_
      simp [N2, hodd]
    · push_neg at hF2
      set h := F.card / 2 with hh
      have hlt : F.card < c := by omega
      have hh1 : 1 ≤ h := by omega
      have hhh : h + 1 ≤ h' := by omega
      have IH : ∀ β : Traj k, (flips β).Nonempty →
          GoodR (G β F) h (3 * h - 2) (Polynomial.C (N2 β F) * Polynomial.X ^ (2 * h - 1)) :=
        fun β hβ => ih F.card hlt F rfl β hβ hF2
      have hAgood : GoodR (A F) h (3 * h - 2) (∑ β ∈ univ.filter
          (fun β : Traj k => (flips β).Nonempty),
          Polynomial.C (N2 β F) * Polynomial.X ^ (2 * h - 1)) :=
        GoodR.sum _ _ _ (fun β hβ => IH β (mem_filter.1 hβ).2)
      have hT := T_mul_D F
      rw [hE, zero_mul, add_zero] at hT
      have hTgood := hAgood.div hT
      have hz := G_zero F
      rw [hE, zero_add] at hz
      have hzgood := hTgood.X_mul
      rw [← hz] at hzgood
      have hsum : GoodR (∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty),
          (if Compat β β' then G β F else 0)) (h + 1) (3 * h) 0 := by
        have := GoodR.sum (univ.filter (fun β : Traj k => (flips β).Nonempty))
          (fun β => if Compat β β' then G β F else 0) (fun _ => (0 : Polynomial ℤ))
          (e := h + 1) (d := 3 * h) (fun β hβ => by
            split_ifs
            · exact (IH β (mem_filter.1 hβ).2).lift.mono (by omega)
            · exact GoodR.zero _ _)
        simpa using this
      have hS := ((hzgood.mono (show 3 * h - 2 + 1 ≤ 3 * h by omega)).add hsum).X_mul
      by_cases hhe : h' = h + 1
      · -- exactly two flips at the last active site
        have hc2 : (flips β').card = 2 := by omega
        rw [← hhe] at hS
        have hval : (∑ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty), N2 β F) =
            N2 β' F' := by
          by_cases hev : Even F.card
          · rw [sum_N2 F hF2 hev]
            have hev' : Even F'.card := by
              obtain ⟨r, hr⟩ := hev; exact ⟨r + 1, by omega⟩
            have : F'.card - 2 = F.card := by omega
            simp only [N2, hc2, hs, hev', and_self, if_true, this]
          · have hodd : ¬ Even F'.card := by
              rintro ⟨r, hr⟩; exact hev ⟨r - 1, by omega⟩
            have h0 : ∀ β ∈ univ.filter (fun β : Traj k => (flips β).Nonempty), N2 β F = 0 := by
              intro β _; simp [N2, hev]
            rw [Finset.sum_eq_zero h0]
            simp [N2, hodd]
        have hexp : 2 * h' - 1 = (2 * h - 1) + 2 := by omega
        refine (hS.mono (by omega)).congr ?_
        rw [add_zero, ← Finset.sum_mul, ← map_sum, hval, hexp, pow_add]
        ring
      · have := hS.lift_many (h' - (h + 1)) (by omega)
        rw [show h + 1 + (h' - (h + 1)) = h' by omega] at this
        refine (this.mono (by omega)).congr ?_
        have hc2 : (flips β').card ≠ 2 := by omega
        simp [N2, hc2]

/-- **Residue theorem.** `P_m ≡ (2m)! z^(2m-1) (mod 1 - z - z²)`. -/
theorem pxp_moment_residue (m : ℕ) (hm : 1 ≤ m) :
    ∃ P q : Polynomial ℤ, P.natDegree ≤ 3 * m - 2 ∧
      PowerSeries.mk (fun n => M (2 * m) n) * (1 - X - X ^ 2) ^ (m + 1) = (P : PowerSeries ℤ) ∧
      P = Polynomial.C ((2 * m).factorial : ℤ) * Polynomial.X ^ (2 * m - 1) + Dp * q := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hcard : (univ : Finset (Fin (2 * m))).card = 2 * m := by simp
  have hk : 2 * m / 2 = m := by omega
  have hA : GoodR (A (univ : Finset (Fin (2 * m)))) m (3 * m - 2)
      (∑ β ∈ univ.filter (fun β : Traj (2 * m) => (flips β).Nonempty),
        Polynomial.C (N2 β univ) * Polynomial.X ^ (2 * m - 1)) := by
    refine GoodR.sum _ _ _ (fun β hβ => ?_)
    have := goodR_active (2 * m) univ hcard β (mem_filter.1 hβ).2 (by omega)
    rwa [hcard, hk] at this
  have hT := T_mul_D (univ : Finset (Fin (2 * m)))
  rw [E_of_ne (by simp [Finset.univ_eq_empty_iff]), zero_mul, add_zero] at hT
  obtain ⟨P, q, hP, hPe, hq⟩ := hA.div hT
  refine ⟨P, q, hP, ?_, ?_⟩
  · rw [series_M_eq_T]; exact hPe
  · rw [hq, ← Finset.sum_mul, ← map_sum, sum_N2 _ (by omega) (by rw [hcard]; exact even_two_mul m),
      hcard]

/-- **The denominator `(1 - z - z²)^(m+1)` is sharp**: `1 - z - z²` does not divide `P_m`. -/
theorem pxp_denominator_sharp (m : ℕ) (hm : 1 ≤ m) (P : Polynomial ℤ)
    (hP : PowerSeries.mk (fun n => M (2 * m) n) * (1 - X - X ^ 2) ^ (m + 1) = (P : PowerSeries ℤ)) :
    ¬ Dp ∣ P := by
  obtain ⟨P', q, -, hP', hq⟩ := pxp_moment_residue m hm
  have hPP : P = P' := by
    have := hP.symm.trans hP'
    exact Polynomial.coe_inj.1 this
  subst hPP
  rintro ⟨s, hs⟩
  -- evaluate at the root `-ψ = 1/φ` of `1 - z - z²`
  set x : ℝ := -Real.goldenConj with hx
  have hroot : (Dp.map (Int.castRingHom ℝ)).eval x = 0 := by
    simp only [Dp, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, Polynomial.map_pow,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow, hx]
    have := Real.goldenConj_sq
    linear_combination -this
  have h1 := congrArg (fun f : Polynomial ℤ => (f.map (Int.castRingHom ℝ)).eval x) (hq.symm.trans hs)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add, Polynomial.eval_mul,
    hroot, zero_mul, add_zero, Polynomial.map_C, Polynomial.eval_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_X] at h1
  have hxne : x ≠ 0 := by rw [hx]; exact neg_ne_zero.2 Real.goldenConj_ne_zero
  simp [Nat.factorial_ne_zero, hxne] at h1

end APEX.PXP
