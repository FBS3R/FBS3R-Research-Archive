import APEX.Blockade.General.Rational
import APEX.PXP.Residue

/-!
# Range-`r` blockade, all even moments: the residue of the numerator modulo `D_r`

**Theorem (`moment_residue`).**  For `r ≥ 1`, `m ≥ 1`, the numerator `P` of
`(∑ₙ Tr A_{n,r}^{2m} zⁿ) · D_r^{m+1} = P` (degree `≤ (2r+1)(m−1)+1`) satisfies
`P ≡ (2m)! · z^{(r+1)m − r}  (mod D_r = 1 − z − z^{r+1})` in `ℤ[z]`.

Proof: the induction of `Transfer.lean`, tracking residues; lifting by `D_r` kills residues, so
only arrays in which every active site flips exactly twice survive, and between consecutive
active sites there are exactly `r` zero sites (the depth recursion contributes `z^r`).
-/

namespace APEX.Blockade.General

open Finset PowerSeries
open APEX.PXP (Traj flips two_le_card_flips)

variable {k : ℕ}

/-- `GoodR r S e d ρ` : `S · D_r^e = p`, `deg p ≤ d`, and `p ≡ ρ (mod D_r)`. -/
def GoodR (r : ℕ) (S : PowerSeries ℤ) (e d : ℕ) (ρ : Polynomial ℤ) : Prop :=
  ∃ p q : Polynomial ℤ, p.natDegree ≤ d ∧ S * Dser r ^ e = (p : PowerSeries ℤ) ∧ p = ρ + Dpol r * q

lemma GoodR.zero (r e d : ℕ) : GoodR r 0 e d 0 := ⟨0, 0, by simp, by simp, by simp⟩

lemma GoodR.add {r : ℕ} {S S' : PowerSeries ℤ} {e d : ℕ} {ρ ρ' : Polynomial ℤ}
    (h : GoodR r S e d ρ) (h' : GoodR r S' e d ρ') : GoodR r (S + S') e d (ρ + ρ') := by
  obtain ⟨p, q, hp, hS, hq⟩ := h
  obtain ⟨p', q', hp', hS', hq'⟩ := h'
  refine ⟨p + p', q + q', (Polynomial.natDegree_add_le _ _).trans (max_le hp hp'), ?_, ?_⟩
  · rw [add_mul, hS, hS', Polynomial.coe_add]
  · rw [hq, hq']; ring

lemma GoodR.sum {r : ℕ} {ι : Type*} (s : Finset ι) (S : ι → PowerSeries ℤ) (ρ : ι → Polynomial ℤ)
    {e d : ℕ} (h : ∀ i ∈ s, GoodR r (S i) e d (ρ i)) :
    GoodR r (∑ i ∈ s, S i) e d (∑ i ∈ s, ρ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GoodR.zero r e d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma GoodR.mono {r : ℕ} {S : PowerSeries ℤ} {e d d' : ℕ} {ρ : Polynomial ℤ} (h : GoodR r S e d ρ)
    (hd : d ≤ d') : GoodR r S e d' ρ := by
  obtain ⟨p, q, hp, hS, hq⟩ := h
  exact ⟨p, q, hp.trans hd, hS, hq⟩

lemma GoodR.congr {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} {ρ ρ' : Polynomial ℤ}
    (h : GoodR r S e d ρ) (hr : ρ = ρ') : GoodR r S e d ρ' := hr ▸ h

lemma GoodR.lift {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} {ρ : Polynomial ℤ} (h : GoodR r S e d ρ) :
    GoodR r S (e + 1) (d + (r + 1)) 0 := by
  obtain ⟨p, q, hp, hS, hq⟩ := h
  refine ⟨p * Dpol r, p, (Polynomial.natDegree_mul_le).trans (add_le_add hp (natDegree_Dpol_le r)),
    ?_, ?_⟩
  · rw [pow_succ, ← mul_assoc, hS, Polynomial.coe_mul, coe_Dpol]
  · ring

lemma GoodR.lift_many {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} {ρ : Polynomial ℤ}
    (h : GoodR r S e d ρ) (j : ℕ) (hj : 1 ≤ j) : GoodR r S (e + j) (d + (r + 1) * j) 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · simpa using h.lift
    · have := (ih hj').lift
      rw [show e + (j + 1) = e + j + 1 by ring,
        show d + (r + 1) * (j + 1) = d + (r + 1) * j + (r + 1) by ring]
      exact this

lemma GoodR.X_mul {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} {ρ : Polynomial ℤ} (h : GoodR r S e d ρ) :
    GoodR r (X * S) e (d + 1) (Polynomial.X * ρ) := by
  obtain ⟨p, q, hp, hS, hq⟩ := h
  refine ⟨Polynomial.X * p, Polynomial.X * q, ?_, ?_, ?_⟩
  · refine (Polynomial.natDegree_mul_le).trans ?_
    have := Polynomial.natDegree_X_le (R := ℤ)
    omega
  · rw [mul_assoc, hS, Polynomial.coe_mul, Polynomial.coe_X]
  · rw [hq]; ring

lemma GoodR.div {r : ℕ} {S S' : PowerSeries ℤ} {e d : ℕ} {ρ : Polynomial ℤ} (h : GoodR r S e d ρ)
    (hS' : S' * Dser r = S) : GoodR r S' (e + 1) d ρ := by
  obtain ⟨p, q, hp, hS, hq⟩ := h
  exact ⟨p, q, hp, by rw [pow_succ', ← mul_assoc, hS', hS], hq⟩

lemma GoodR.ite {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} {ρ : Polynomial ℤ} (P : Prop) [Decidable P]
    (h : P → GoodR r S e d ρ) : GoodR r (if P then S else 0) e d (if P then ρ else 0) := by
  split_ifs with hp
  · exact h hp
  · exact GoodR.zero r e d


/-- Residue of the free series at `|F| = 2(g+1)`. -/
noncomputable def ρΦ (r g : ℕ) : Polynomial ℤ :=
  Polynomial.C (((2 * (g + 1)).factorial : ℕ) : ℤ) * Polynomial.X ^ ((r + 1) * g + 1)

lemma sum_two_flips [NeZero k] (F : Finset (Fin k)) (c : Polynomial ℤ) :
    ∑ β ∈ APEX.Blockade.General.act k,
      (if flips β ⊆ F then (if (flips β).card = 2 then c else 0) else 0) =
      Polynomial.C ((F.card * (F.card - 1) : ℕ) : ℤ) * c := by
  have : ∀ β ∈ act k, (if flips β ⊆ F then (if (flips β).card = 2 then c else 0) else 0) =
      if (flips β).card = 2 ∧ flips β ⊆ F then c else 0 := by
    intro β _; split_ifs <;> simp_all
  rw [sum_congr rfl this, ← sum_filter, sum_const]
  have hfil : (act k).filter (fun β : Traj k => (flips β).card = 2 ∧ flips β ⊆ F) =
      univ.filter (fun β : Traj k => (flips β).card = 2 ∧ flips β ⊆ F) := by
    ext β
    simp only [act, mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨card_pos.1 (by omega), h⟩
  rw [hfil, APEX.PXP.card_two_flips_in, nsmul_eq_mul, ← Polynomial.C_eq_natCast]

theorem goodR_main [NeZero k] {r : ℕ} (hr : 1 ≤ r) :
    ∀ (g : ℕ) (F : Finset (Fin k)), F.card = 2 * (g + 1) →
      GoodR r (Φ r F) (g + 2) ((2 * r + 1) * g + 1) (ρΦ r g) ∧
      ∀ j, 1 ≤ j → j ≤ r → ∀ σ : St k, Dep r σ j →
        GoodR r (Gs r σ F) (g + 2) ((2 * r + 1) * g + r + 1 + j)
          (Polynomial.X ^ j * ρΦ r g) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro F hc
  have hF0 : F ≠ ∅ := by rintro rfl; simp at hc
  have hE : Ec F = 0 := by simp [Ec, hF0]
  -- active terms
  have hact : ∀ β ∈ act k, flips β ⊆ F → ∀ σ' : St k, Dep r σ' r →
      GoodR r (Gs r σ' (F \ flips β)) (g + 1) ((2 * r + 1) * g)
        (if (flips β).card = 2 then
          Polynomial.C (((2 * g).factorial : ℕ) : ℤ) * Polynomial.X ^ ((r + 1) * g) else 0) := by
    intro β hβ hs σ' hσ'
    have h2 := two_le_card_flips (mem_filter.1 hβ).2
    obtain ⟨t, ht⟩ := APEX.PXP.card_flips_even β
    have hcard : (F \ flips β).card = 2 * (g + 1) - (flips β).card := by
      rw [card_sdiff_of_subset hs, hc]
    have hle := card_le_card hs
    by_cases he : F \ flips β = ∅
    · rw [he]
      have h1 : GoodR r (Gs r σ' ∅) 1 0 1 :=
        ⟨1, 0, by simp, by rw [pow_one, Gs_dep_r_empty (by omega) hσ', Polynomial.coe_one],
          by simp⟩
      have hcF : (flips β).card = 2 * (g + 1) := by
        have := congrArg card he; rw [hcard] at this; simp at this; omega
      rcases Nat.eq_zero_or_pos g with rfl | hg
      · rw [if_pos (by omega)]
        refine (h1.mono (by omega)).congr ?_
        simp
      · have := h1.lift_many g hg
        rw [show 1 + g = g + 1 by ring, zero_add] at this
        rw [if_neg (by omega)]
        exact this.mono (arith2 r g)
    · have hge : 2 ≤ (F \ flips β).card := by
        have := card_pos.2 (nonempty_iff_ne_empty.2 he); omega
      obtain ⟨g', hg'⟩ : ∃ g', (F \ flips β).card = 2 * (g' + 1) :=
        ⟨(F \ flips β).card / 2 - 1, by omega⟩
      have hgg : g' + 1 ≤ g := by omega
      have IH := ((ih g' (by omega) (F \ flips β) hg').2 r hr le_rfl σ' hσ')
      rw [show (2 * r + 1) * g' + r + 1 + r = (2 * r + 1) * (g' + 1) by ring] at IH
      by_cases h2' : (flips β).card = 2
      · have hg1 : g = g' + 1 := by omega
        subst hg1
        rw [if_pos h2']
        refine (IH.mono le_rfl).congr ?_
        unfold ρΦ
        rw [← mul_assoc, mul_comm (Polynomial.X ^ r), mul_assoc, ← pow_add]
        congr 2
        ring
      · rw [if_neg h2']
        have := IH.lift_many (g - (g' + 1)) (by omega)
        rw [show g' + 2 + (g - (g' + 1)) = g + 1 by omega] at this
        exact this.mono (arith1 r g g' hgg)
  -- free state
  have hΦ : GoodR r (Φ r F) (g + 2) ((2 * r + 1) * g + 1) (ρΦ r g) := by
    have hm := Φ_mul_D (by omega : 0 < r) F
    rw [hE, zero_mul, zero_add] at hm
    have hs := GoodR.sum (act k) (fun β => if flips β ⊆ F then
        Gs r (step r free β) (F \ flips β) else 0)
      (fun β => if flips β ⊆ F then (if (flips β).card = 2 then
          Polynomial.C (((2 * g).factorial : ℕ) : ℤ) * Polynomial.X ^ ((r + 1) * g) else 0) else 0)
      (e := g + 1) (d := (2 * r + 1) * g)
      (fun β hβ => GoodR.ite _ (fun hs => hact β hβ hs _ (dep_step_act free (mem_filter.1 hβ).2)))
    refine (hs.X_mul.div hm).congr ?_
    rw [sum_two_flips, hc, ρΦ]
    rw [show 2 * (g + 1) = 2 * g + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    simp only [Polynomial.C_mul, Polynomial.C_eq_natCast]
    push_cast
    rw [pow_succ]
    ring
  refine ⟨hΦ, ?_⟩
  intro j hj1
  induction j with
  | zero => omega
  | succ j ihj =>
    intro hjr σ hσ
    rw [Gs_dep (by omega) hσ, hE, zero_add]
    have hz : GoodR r (Gs r (step r σ zero) F) (g + 2) ((2 * r + 1) * g + r + 1 + j)
        (Polynomial.X ^ j * ρΦ r g) := by
      have hd := dep_step_zero (by omega) hjr hσ
      rw [Nat.add_sub_cancel] at hd
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rw [Gs_congr (by omega) F (dep_zero_free hd), pow_zero, one_mul]
        exact hΦ.mono (by omega)
      · exact ihj hjpos (by omega) _ hd
    have hs := GoodR.sum (act k) (fun β => if Disjoint (occ β) (σ 0) ∧ flips β ⊆ F then
        Gs r (step r σ β) (F \ flips β) else 0) (fun _ => (0 : Polynomial ℤ))
      (e := g + 2) (d := (2 * r + 1) * g + r + 1 + j)
      (fun β hβ => by
        have := GoodR.ite (Disjoint (occ β) (σ 0) ∧ flips β ⊆ F) (fun hs =>
          ((hact β hβ hs.2 _ (dep_step_act σ (mem_filter.1 hβ).2)).lift).mono
            (show (2 * r + 1) * g + (r + 1) ≤ (2 * r + 1) * g + r + 1 + j by omega))
        simpa using this)
    have := (hz.add hs).X_mul
    rw [show (2 * r + 1) * g + r + 1 + j + 1 = (2 * r + 1) * g + r + 1 + (j + 1) by ring] at this
    refine this.congr ?_
    simp only [sum_const_zero, add_zero]
    ring

/-- **Milestone (b): residue theorem.** -/
theorem moment_residue {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    ∃ P q : Polynomial ℤ, P.natDegree ≤ (2 * r + 1) * (m - 1) + 1 ∧
      PowerSeries.mk (fun n => Mk (2 * m) r n) * (1 - X - X ^ (r + 1)) ^ (m + 1) =
        (P : PowerSeries ℤ) ∧
      P = Polynomial.C (((2 * m).factorial : ℕ) : ℤ) * Polynomial.X ^ ((r + 1) * m - r) +
        (1 - Polynomial.X - Polynomial.X ^ (r + 1)) * q := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have h := (goodR_main hr (m - 1) (univ : Finset (Fin (2 * m)))
    (by rw [card_univ, Fintype.card_fin]; omega)).1
  rw [show m - 1 + 2 = m + 1 by omega] at h
  obtain ⟨P, q, hP, hS, hq⟩ := h
  refine ⟨P, q, hP, ?_, ?_⟩
  · rw [series_Mk_eq_Φ hr]; exact hS
  · rw [hq, ρΦ, Dpol, show m - 1 + 1 = m by omega, show (r + 1) * (m - 1) + 1 = (r + 1) * m - r by
      rcases m with _ | m
      · omega
      · rw [show m + 1 - 1 = m by omega]; ring_nf; omega]

end APEX.Blockade.General

