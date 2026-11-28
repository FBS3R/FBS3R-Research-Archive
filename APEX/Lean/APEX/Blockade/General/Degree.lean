import APEX.Blockade.General.Residue

/-!
# Range-`r` blockade, all even moments: exact numerator degree and leading coefficient

**Theorem (`moment_exact`).**  For `r ≥ 1`, `m ≥ 1` the numerator `P` of
`(∑ₙ Tr A_{n,r}^{2m} zⁿ) · D_r^{m+1} = P` has `deg P = (2r+1)(m−1)+1` exactly, and its leading
coefficient is `Lc m`, an integer defined without reference to `r` (`(−1)^{m−1} Lc m` counts
chains of `m` two-flip trajectories with flip sets partitioning the `2m` times and consecutive
ones never simultaneously occupied); `(−1)^{m−1} Lc m ≥ 1`.

**Theorem (`conj_general`).**  `ConjGeneral` of `Moments.lean` holds.
-/

namespace APEX.Blockade.General

open Finset PowerSeries
open APEX.PXP (Traj flips two_le_card_flips)

variable {k : ℕ}

/-- `GoodT r S e d c` : `S · D_r^e = p`, `deg p ≤ d`, `coeff p d = c`. -/
def GoodT (r : ℕ) (S : PowerSeries ℤ) (e d : ℕ) (c : ℤ) : Prop :=
  ∃ p : Polynomial ℤ, p.natDegree ≤ d ∧ S * Dser r ^ e = (p : PowerSeries ℤ) ∧ p.coeff d = c

lemma GoodT.zero (r e d : ℕ) : GoodT r 0 e d 0 := ⟨0, by simp, by simp, by simp⟩

lemma GoodT.add {r : ℕ} {S S' : PowerSeries ℤ} {e d : ℕ} {c c' : ℤ} (h : GoodT r S e d c)
    (h' : GoodT r S' e d c') : GoodT r (S + S') e d (c + c') := by
  obtain ⟨p, hp, hS, hc⟩ := h
  obtain ⟨p', hp', hS', hc'⟩ := h'
  refine ⟨p + p', (Polynomial.natDegree_add_le _ _).trans (max_le hp hp'), ?_, ?_⟩
  · rw [add_mul, hS, hS', Polynomial.coe_add]
  · rw [Polynomial.coeff_add, hc, hc']

lemma GoodT.sum {r : ℕ} {ι : Type*} (s : Finset ι) (S : ι → PowerSeries ℤ) (c : ι → ℤ) {e d : ℕ}
    (h : ∀ i ∈ s, GoodT r (S i) e d (c i)) : GoodT r (∑ i ∈ s, S i) e d (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GoodT.zero r e d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (mem_insert_self _ _)).add (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma GoodT.ite {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} {c : ℤ} (P : Prop) [Decidable P]
    (h : P → GoodT r S e d c) : GoodT r (if P then S else 0) e d (if P then c else 0) := by
  split_ifs with hp
  · exact h hp
  · exact GoodT.zero r e d

lemma GoodT.congr {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} {c c' : ℤ} (h : GoodT r S e d c)
    (hc : c = c') : GoodT r S e d c' := hc ▸ h

lemma coeff_Dpol_top {r : ℕ} (hr : 1 ≤ r) : (Dpol r).coeff (r + 1) = -1 := by
  simp [Dpol, Polynomial.coeff_one, Polynomial.coeff_X]
  omega

lemma GoodT.lift {r : ℕ} (hr : 1 ≤ r) {S : PowerSeries ℤ} {e d : ℕ} {c : ℤ} (h : GoodT r S e d c) :
    GoodT r S (e + 1) (d + (r + 1)) (-c) := by
  obtain ⟨p, hp, hS, hc⟩ := h
  refine ⟨p * Dpol r, (Polynomial.natDegree_mul_le).trans (add_le_add hp (natDegree_Dpol_le r)),
    ?_, ?_⟩
  · rw [pow_succ, ← mul_assoc, hS, Polynomial.coe_mul, coe_Dpol]
  · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hp (natDegree_Dpol_le r), hc,
      coeff_Dpol_top hr]
    ring

lemma GoodT.X_mul {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} {c : ℤ} (h : GoodT r S e d c) :
    GoodT r (X * S) e (d + 1) c := by
  obtain ⟨p, hp, hS, hc⟩ := h
  refine ⟨Polynomial.X * p, ?_, ?_, ?_⟩
  · refine (Polynomial.natDegree_mul_le).trans ?_
    have := Polynomial.natDegree_X_le (R := ℤ)
    omega
  · rw [mul_assoc, hS, Polynomial.coe_mul, Polynomial.coe_X]
  · rw [Polynomial.coeff_X_mul, hc]

lemma GoodT.div {r : ℕ} {S S' : PowerSeries ℤ} {e d : ℕ} {c : ℤ} (h : GoodT r S e d c)
    (hS' : S' * Dser r = S) : GoodT r S' (e + 1) d c := by
  obtain ⟨p, hp, hS, hc⟩ := h
  exact ⟨p, hp, by rw [pow_succ', ← mul_assoc, hS', hS], hc⟩

lemma GoodT.of_good_lt {r : ℕ} {S : PowerSeries ℤ} {e d d' : ℕ} (h : Good r S e d) (hd : d < d') :
    GoodT r S e d' 0 := by
  obtain ⟨p, hp, hS⟩ := h
  exact ⟨p, hp.trans hd.le, hS, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)⟩

lemma GoodT.toGood {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} {c : ℤ} (h : GoodT r S e d c) :
    Good r S e d := by
  obtain ⟨p, hp, hS, -⟩ := h
  exact ⟨p, hp, hS⟩

/-! ### The top-coefficient recursion (independent of `r`) -/

/-- Signed chain count: last active trajectory `β`, remaining flip set `F`. -/
def τ : ℕ → Traj k → Finset (Fin k) → ℤ
  | 0, _, F => if F = ∅ then 1 else 0
  | g + 1, β, F => if F = ∅ then 1 else
      -∑ β' ∈ act k, if (flips β').card = 2 ∧ flips β' ⊆ F ∧ Disjoint (occ β') (occ β) then
        τ g β' (F \ flips β') else 0

/-- Contribution of an active trajectory `β` placed at flip set `F`. -/
def cT (g : ℕ) (β : Traj k) (F : Finset (Fin k)) : ℤ :=
  if (flips β).card = 2 then τ g β (F \ flips β) else 0

/-- Top coefficient of the free series. -/
def cΦ (g : ℕ) (F : Finset (Fin k)) : ℤ :=
  ∑ β ∈ act k, if flips β ⊆ F then cT g β F else 0

/-- Top coefficient of a depth-`j` series. -/
def cD (g : ℕ) (σ : St k) (j : ℕ) (F : Finset (Fin k)) : ℤ :=
  -∑ β ∈ act k, if Disjoint (occ β) (σ (j - 1)) ∧ flips β ⊆ F then cT g β F else 0

lemma arith3 (r g g' : ℕ) (hr : 1 ≤ r) (h : g' + 1 < g) :
    (2 * r + 1) * (g' + 1) + (r + 1) * (g - (g' + 1)) < (2 * r + 1) * g := by
  obtain ⟨d, rfl⟩ : ∃ d, g = g' + 1 + (d + 1) := ⟨g - (g' + 2), by omega⟩
  rw [show g' + 1 + (d + 1) - (g' + 1) = d + 1 by omega]
  nlinarith

lemma arith4 (r g : ℕ) (hr : 1 ≤ r) (hg : 1 ≤ g) : (r + 1) * g < (2 * r + 1) * g := by nlinarith

theorem goodT_main [NeZero k] {r : ℕ} (hr : 1 ≤ r) :
    ∀ (g : ℕ) (F : Finset (Fin k)), F.card = 2 * (g + 1) →
      GoodT r (Φ r F) (g + 2) ((2 * r + 1) * g + 1) (cΦ g F) ∧
      ∀ j, 1 ≤ j → j ≤ r → ∀ σ : St k, Dep r σ j →
        GoodT r (Gs r σ F) (g + 2) ((2 * r + 1) * g + r + 1 + j) (cD g σ j F) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro F hc
  have hF0 : F ≠ ∅ := by rintro rfl; simp at hc
  have hE : Ec F = 0 := by simp [Ec, hF0]
  -- active terms
  have hact : ∀ β ∈ act k, flips β ⊆ F → ∀ σ : St k,
      GoodT r (Gs r (step r σ β) (F \ flips β)) (g + 1) ((2 * r + 1) * g) (cT g β F) := by
    intro β hβ hs σ
    have hσ' := dep_step_act (r := r) σ (mem_filter.1 hβ).2
    have h2 := two_le_card_flips (mem_filter.1 hβ).2
    obtain ⟨t, ht⟩ := APEX.PXP.card_flips_even β
    have hcard : (F \ flips β).card = 2 * (g + 1) - (flips β).card := by
      rw [card_sdiff_of_subset hs, hc]
    have hle := card_le_card hs
    by_cases he : F \ flips β = ∅
    · rw [he]
      have hgood : Good r (Gs r (step r σ β) ∅) 1 0 :=
        ⟨1, by simp, by rw [pow_one, Gs_dep_r_empty (by omega) hσ', Polynomial.coe_one]⟩
      have hcF : (flips β).card = 2 * (g + 1) := by
        have := congrArg card he; rw [hcard] at this; simp at this; omega
      rcases Nat.eq_zero_or_pos g with rfl | hg
      · have h1 : GoodT r (Gs r (step r σ β) ∅) 1 0 1 :=
          ⟨1, by simp, by rw [pow_one, Gs_dep_r_empty (by omega) hσ', Polynomial.coe_one],
            by simp⟩
        refine h1.congr ?_
        rw [cT, if_pos (by omega), he]; rfl
      · have := hgood.lift_many g
        rw [show 1 + g = g + 1 by ring, zero_add] at this
        refine (GoodT.of_good_lt this (arith4 r g hr hg)).congr ?_
        rw [cT, if_neg (by omega)]
    · have hge : 2 ≤ (F \ flips β).card := by
        have := card_pos.2 (nonempty_iff_ne_empty.2 he); omega
      obtain ⟨g', hg'⟩ : ∃ g', (F \ flips β).card = 2 * (g' + 1) :=
        ⟨(F \ flips β).card / 2 - 1, by omega⟩
      have hgg : g' + 1 ≤ g := by omega
      have IH := ((ih g' (by omega) (F \ flips β) hg').2 r hr le_rfl _ hσ')
      rw [show (2 * r + 1) * g' + r + 1 + r = (2 * r + 1) * (g' + 1) by ring] at IH
      by_cases h2' : (flips β).card = 2
      · have hg1 : g = g' + 1 := by omega
        subst hg1
        refine IH.congr ?_
        rw [cT, if_pos h2', cD, τ, if_neg he]
        congr 1
        refine sum_congr rfl (fun β' _ => ?_)
        have hocc : step r σ β (r - 1) = occ β := by
          simp only [step]; rw [if_neg (by omega), empty_union]
        rw [hocc, cT]
        by_cases c1 : Disjoint (occ β') (occ β) <;> by_cases c2 : flips β' ⊆ F \ flips β <;>
          by_cases c3 : (flips β').card = 2 <;> simp [c1, c2, c3]
      · have := (IH.toGood).lift_many (g - (g' + 1))
        rw [show g' + 2 + (g - (g' + 1)) = g + 1 by omega] at this
        refine (GoodT.of_good_lt this (arith3 r g g' hr (by omega))).congr ?_
        rw [cT, if_neg h2']
  -- free state
  have hΦ : GoodT r (Φ r F) (g + 2) ((2 * r + 1) * g + 1) (cΦ g F) := by
    have hm := Φ_mul_D (by omega : 0 < r) F
    rw [hE, zero_mul, zero_add] at hm
    have hs := GoodT.sum (act k) (fun β => if flips β ⊆ F then
        Gs r (step r free β) (F \ flips β) else 0)
      (fun β => if flips β ⊆ F then cT g β F else 0) (e := g + 1) (d := (2 * r + 1) * g)
      (fun β hβ => GoodT.ite _ (fun hs => hact β hβ hs free))
    exact hs.X_mul.div hm
  refine ⟨hΦ, ?_⟩
  intro j hj1
  induction j with
  | zero => omega
  | succ j ihj =>
    intro hjr σ hσ
    rw [Gs_dep (by omega) hσ, hE, zero_add]
    have hd := dep_step_zero (by omega) hjr hσ
    rw [Nat.add_sub_cancel] at hd
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · -- j = 1: the zero branch is strictly lower, the active branch is tight
      have hz : GoodT r (Gs r (step r σ zero) F) (g + 2) ((2 * r + 1) * g + r + 1) 0 := by
        rw [Gs_congr (by omega) F (dep_zero_free hd)]
        exact GoodT.of_good_lt hΦ.toGood (by omega)
      have hs := GoodT.sum (act k) (fun β => if Disjoint (occ β) (σ 0) ∧ flips β ⊆ F then
          Gs r (step r σ β) (F \ flips β) else 0)
        (fun β => if Disjoint (occ β) (σ 0) ∧ flips β ⊆ F then -cT g β F else 0)
        (e := g + 2) (d := (2 * r + 1) * g + (r + 1))
        (fun β hβ => GoodT.ite _ (fun hs => (hact β hβ hs.2 σ).lift hr))
      rw [show (2 * r + 1) * g + (r + 1) = (2 * r + 1) * g + r + 1 by ring] at hs
      refine ((hz.add hs).X_mul).congr ?_
      rw [zero_add, cD, Nat.sub_self, ← sum_neg_distrib]
      refine sum_congr rfl (fun β _ => ?_)
      split_ifs <;> simp
    · have hz := ihj hjpos (by omega) _ hd
      have hs : GoodT r (∑ β ∈ act k, (if Disjoint (occ β) (σ 0) ∧ flips β ⊆ F then
          Gs r (step r σ β) (F \ flips β) else 0)) (g + 2) ((2 * r + 1) * g + r + 1 + j) 0 := by
        refine GoodT.of_good_lt (d := (2 * r + 1) * g + (r + 1)) ?_ (by omega)
        refine Good.sum _ _ (fun β hβ => Good.ite _ (fun hs => ?_))
        exact ((hact β hβ hs.2 σ).toGood).lift
      refine ((hz.add hs).X_mul).congr ?_
      have : step r σ zero (j - 1) = σ (j + 1 - 1) := by
        simp only [step, occ_zero, union_empty]
        rw [if_pos (by omega), show j - 1 + 1 = j + 1 - 1 by omega]
      rw [add_zero, cD, cD, this]

/-! ### Sign and non-vanishing of the leading coefficient -/

lemma τ_sign [NeZero k] : ∀ (g : ℕ) (β : Traj k) (F : Finset (Fin k)), F.card = 2 * g →
    0 ≤ (-1 : ℤ) ^ g * τ g β F
  | 0, β, F, h => by
    have : F = ∅ := card_eq_zero.1 (by omega)
    simp [τ, this]
  | g + 1, β, F, h => by
    have hF : F ≠ ∅ := by rintro rfl; simp at h
    rw [τ, if_neg hF, show ∀ S : ℤ, (-1 : ℤ) ^ (g + 1) * -S = (-1) ^ g * S from fun S => by ring,
      mul_sum]
    refine sum_nonneg (fun β' _ => ?_)
    split_ifs with hc
    · exact τ_sign g β' _ (by rw [card_sdiff_of_subset hc.2.1, h, hc.1]; omega)
    · simp

/-- Times `≥ 2a`. -/
def Fa (m a : ℕ) : Finset (Fin (2 * m)) := univ.filter (fun t => 2 * a ≤ t.val)

lemma card_Fa (m a : ℕ) (ha : a ≤ m) : (Fa m a).card = 2 * m - 2 * a := by
  rw [← card_range (2 * m - 2 * a)]
  symm
  apply card_bij (fun i hi => (⟨2 * a + i, by rw [mem_range] at hi; omega⟩ : Fin (2 * m)))
  · intro i _; simp [Fa]
  · intro i _ j _ h; simp only [Fin.ext_iff] at h; omega
  · intro t ht
    simp only [Fa, mem_filter, mem_univ, true_and] at ht
    exact ⟨t.val - 2 * a, by rw [mem_range]; omega, by ext; simp only; omega⟩

/-- The pulse at pair `a`: occupied exactly at time `2a+1`. -/
def pul (m a : ℕ) : Traj (2 * m) := fun t => decide (t.val = 2 * a + 1)

lemma pul_eq_ival {m a : ℕ} (ha : a < m) :
    pul m a = APEX.PXP.ival (⟨2 * a, by omega⟩ : Fin (2 * m)) ⟨2 * a + 1, by omega⟩ := by
  funext t
  simp only [pul, APEX.PXP.ival, Fin.lt_def, Fin.le_def]
  apply Bool.decide_congr
  omega

lemma flips_pul {m a : ℕ} (ha : a < m) :
    flips (pul m a) = {⟨2 * a, by omega⟩, ⟨2 * a + 1, by omega⟩} := by
  rw [pul_eq_ival ha, APEX.PXP.flips_ival (by rw [Fin.lt_def]; simp)]

lemma occ_pul (m a : ℕ) (t : Fin (2 * m)) : t ∈ occ (pul m a) ↔ t.val = 2 * a + 1 := by
  simp [occ, pul]

lemma τ_pos {m : ℕ} (hm : 1 ≤ m) : ∀ d a : ℕ, a + d = m → ∀ β : Traj (2 * m),
    (∀ t : Fin (2 * m), t.val = 2 * a + 1 → β t = false) → 1 ≤ (-1 : ℤ) ^ d * τ d β (Fa m a)
  | 0, a, h, β, _ => by
    have : Fa m a = ∅ := by
      ext t; simp only [Fa, mem_filter, mem_univ, true_and, notMem_empty, iff_false]; omega
    simp [τ, this]
  | d + 1, a, h, β, hβ => by
    have : NeZero (2 * m) := ⟨by omega⟩
    have ha : a < m := by omega
    have hF : Fa m a ≠ ∅ := by
      intro he
      have : (⟨2 * a, by omega⟩ : Fin (2 * m)) ∈ Fa m a := by simp [Fa]
      rw [he] at this; simp at this
    rw [τ, if_neg hF, show ∀ S : ℤ, (-1 : ℤ) ^ (d + 1) * -S = (-1) ^ d * S from fun S => by ring,
      mul_sum]
    have hP : pul m a ∈ act (2 * m) := by
      simp only [act, mem_filter, mem_univ, true_and, flips_pul ha]; simp
    have hc : (flips (pul m a)).card = 2 ∧ flips (pul m a) ⊆ Fa m a ∧
        Disjoint (occ (pul m a)) (occ β) := by
      refine ⟨by rw [flips_pul ha]; exact card_pair (by simp [Fin.ext_iff]), ?_, ?_⟩
      · rw [flips_pul ha]
        intro t ht
        simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl <;> simp [Fa]
      · rw [disjoint_left]
        intro t h1 h2
        rw [occ_pul] at h1
        simp [occ, hβ t h1] at h2
    have hsd : Fa m a \ flips (pul m a) = Fa m (a + 1) := by
      rw [flips_pul ha]
      ext t
      simp only [Fa, mem_sdiff, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        Fin.ext_iff]
      omega
    have hterm : 1 ≤ (-1 : ℤ) ^ d * (if (flips (pul m a)).card = 2 ∧ flips (pul m a) ⊆ Fa m a ∧
        Disjoint (occ (pul m a)) (occ β) then τ d (pul m a) (Fa m a \ flips (pul m a)) else 0) := by
      rw [if_pos hc, hsd]
      exact τ_pos hm d (a + 1) (by omega) (pul m a) (fun t ht => by simp [pul]; omega)
    refine hterm.trans (single_le_sum (f := fun β' => (-1 : ℤ) ^ d *
      (if (flips β').card = 2 ∧ flips β' ⊆ Fa m a ∧ Disjoint (occ β') (occ β) then
        τ d β' (Fa m a \ flips β') else 0)) (fun β' _ => ?_) hP)
    split_ifs with hc'
    · refine τ_sign d β' _ ?_
      rw [card_sdiff_of_subset hc'.2.1, hc'.1]
      have := card_Fa m a ha.le
      omega
    · simp

/-- The leading coefficient (defined without reference to `r`). -/
def Lc (m : ℕ) : ℤ := cΦ (m - 1) (univ : Finset (Fin (2 * m)))

theorem Lc_sign {m : ℕ} (hm : 1 ≤ m) : 1 ≤ (-1 : ℤ) ^ (m - 1) * Lc m := by
  have : NeZero (2 * m) := ⟨by omega⟩
  rw [Lc, cΦ, mul_sum]
  have hP : pul m 0 ∈ act (2 * m) := by
    simp only [act, mem_filter, mem_univ, true_and, flips_pul (show 0 < m by omega)]; simp
  have hsd : (univ : Finset (Fin (2 * m))) \ flips (pul m 0) = Fa m 1 := by
    rw [flips_pul (by omega)]
    ext t
    simp only [Fa, mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton, mem_filter,
      Fin.ext_iff]
    omega
  have h2 : (flips (pul m 0)).card = 2 := by
    rw [flips_pul (by omega)]; exact card_pair (by simp [Fin.ext_iff])
  have hterm : 1 ≤ (-1 : ℤ) ^ (m - 1) *
      (if flips (pul m 0) ⊆ univ then cT (m - 1) (pul m 0) univ else 0) := by
    rw [if_pos (subset_univ _), cT, if_pos h2, hsd]
    exact τ_pos hm (m - 1) 1 (by omega) (pul m 0) (fun t ht => by simp [pul]; omega)
  refine hterm.trans (single_le_sum (f := fun β => (-1 : ℤ) ^ (m - 1) *
    (if flips β ⊆ univ then cT (m - 1) β univ else 0)) (fun β _ => ?_) hP)
  rw [if_pos (subset_univ _), cT]
  split_ifs with h2'
  · refine τ_sign (m - 1) β _ ?_
    rw [card_sdiff_of_subset (subset_univ _), h2', card_univ, Fintype.card_fin]; omega
  · simp

theorem Lc_ne_zero {m : ℕ} (hm : 1 ≤ m) : Lc m ≠ 0 := by
  intro h
  have := Lc_sign hm
  rw [h, mul_zero] at this
  omega

/-- **Milestone (c)**: exact numerator degree `(2r+1)(m−1)+1` with the `r`-independent leading
coefficient `Lc m ≠ 0`. -/
theorem moment_exact {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    ∃ P : Polynomial ℤ, P.natDegree = (2 * r + 1) * (m - 1) + 1 ∧
      PowerSeries.mk (fun n => Mk (2 * m) r n) * (1 - X - X ^ (r + 1)) ^ (m + 1) =
        (P : PowerSeries ℤ) ∧ P.leadingCoeff = Lc m := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have h := (goodT_main hr (m - 1) (univ : Finset (Fin (2 * m)))
    (by rw [card_univ, Fintype.card_fin]; omega)).1
  rw [show m - 1 + 2 = m + 1 by omega] at h
  obtain ⟨P, hP, hS, hc⟩ := h
  have hdeg : P.natDegree = (2 * r + 1) * (m - 1) + 1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hP (by rw [hc]; exact Lc_ne_zero hm)
  refine ⟨P, hdeg, ?_, ?_⟩
  · rw [series_Mk_eq_Φ hr]; exact hS
  · rw [Polynomial.leadingCoeff, hdeg, hc]; rfl

/-- **`ConjGeneral` (Moments.lean) is a theorem.** -/
theorem conj_general : ConjGeneral := by
  intro m r hm hr
  obtain ⟨P, hdeg, hS, -⟩ := moment_exact hr hm
  obtain ⟨P', q, -, hS', hq⟩ := moment_residue hr hm
  have hPP : P = P' := Polynomial.coe_inj.1 (hS.symm.trans hS')
  subst hPP
  refine ⟨P, hdeg, hS, q, ?_⟩
  rw [hq]; ring

end APEX.Blockade.General

