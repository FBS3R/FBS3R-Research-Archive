import APEX.Blockade.Fourth
import APEX.PXP.Walks

/-!
# Range-`r` blockade, all moments: the site transfer system and its rationality

Trajectory arrays are processed site by site.  The state `σ : ℕ → Finset (Fin k)` records,
for each of the next `r` sites, the set of times at which that site must be empty (because a
previous site within distance `r` is occupied then).  `N r n σ F` counts arrays of `n`
trajectories with pairwise disjoint flip sets of union `F`, the range-`r` blockade inside the
array and the constraints `σ` at the start.

Main result (`good_free`): for `r ≥ 1` and `|F| = 2(g+1)`, the generating series
`Φ F = ∑ₙ N r n ∅ F zⁿ` satisfies `Φ F · D_r^{g+2} ∈ ℤ[z]` with degree `≤ (2r+1) g + 1`.
-/

namespace APEX.Blockade.General

open Finset PowerSeries
open APEX.PXP (Traj flips mem_flips Compat card_flips_even two_le_card_flips flips_eq_empty_iff
  filter_flips_empty)

variable {k : ℕ}

/-- Occupied times of a trajectory. -/
def occ (β : Traj k) : Finset (Fin k) := univ.filter (fun t => β t = true)

/-- Constraint states. -/
abbrev St (k : ℕ) := ℕ → Finset (Fin k)

/-- State after placing `β`. -/
def step (r : ℕ) (σ : St k) (β : Traj k) : St k :=
  fun j => (if j + 1 < r then σ (j + 1) else ∅) ∪ occ β

/-- The transfer count. -/
def N (r : ℕ) : ℕ → St k → Finset (Fin k) → ℕ
  | 0, _, F => if F = ∅ then 1 else 0
  | n + 1, σ, F => ∑ β : Traj k,
      if Disjoint (occ β) (σ 0) ∧ flips β ⊆ F then N r n (step r σ β) (F \ flips β) else 0

/-- Generating series. -/
noncomputable def Gs (r : ℕ) (σ : St k) (F : Finset (Fin k)) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (N r n σ F : ℤ))

/-- The free state. -/
def free : St k := fun _ => ∅

/-- Free-state series. -/
noncomputable def Φ (r : ℕ) (F : Finset (Fin k)) : PowerSeries ℤ := Gs r free F

/-- Empty-array indicator. -/
noncomputable def Ec (F : Finset (Fin k)) : PowerSeries ℤ := if F = ∅ then 1 else 0

lemma Gs_rec (r : ℕ) (σ : St k) (F : Finset (Fin k)) :
    Gs r σ F = Ec F + X * ∑ β : Traj k,
      (if Disjoint (occ β) (σ 0) ∧ flips β ⊆ F then Gs r (step r σ β) (F \ flips β) else 0) := by
  ext n
  cases n with
  | zero =>
    simp only [Gs, coeff_mk, N, map_add, coeff_zero_X_mul, add_zero, Ec]
    split_ifs <;> simp
  | succ n =>
    rw [map_add, coeff_succ_X_mul, map_sum]
    have h0 : coeff (n + 1) (Ec F) = 0 := by unfold Ec; split_ifs <;> simp
    rw [h0, zero_add]
    simp only [Gs, coeff_mk, N]
    push_cast
    refine sum_congr rfl (fun β _ => ?_)
    split_ifs <;> simp [coeff_mk]

lemma N_congr {r : ℕ} (hr : 0 < r) : ∀ (n : ℕ) {σ τ : St k} (F : Finset (Fin k)),
    (∀ i < r, σ i = τ i) → N r n σ F = N r n τ F
  | 0, _, _, _, _ => rfl
  | n + 1, σ, τ, F, h => by
    simp only [N]
    rw [h 0 hr]
    refine sum_congr rfl (fun β _ => ?_)
    split_ifs
    · apply N_congr hr n
      intro i hi
      simp only [step]
      split_ifs with hi'
      · rw [h (i + 1) hi']
      · rfl
    · rfl

lemma Gs_congr {r : ℕ} (hr : 0 < r) {σ τ : St k} (F : Finset (Fin k))
    (h : ∀ i < r, σ i = τ i) : Gs r σ F = Gs r τ F := by
  ext n; simp only [Gs, coeff_mk]; rw [N_congr hr n F h]

/-! ### Inactive trajectories -/

def zero : Traj k := APEX.PXP.zero
def one : Traj k := APEX.PXP.one

lemma occ_zero : occ (zero : Traj k) = ∅ := by
  ext t; simp [occ, zero, APEX.PXP.zero]

lemma occ_one : occ (one : Traj k) = univ := by
  ext t; simp [occ, one, APEX.PXP.one]

lemma occ_eq_empty_iff (β : Traj k) : occ β = ∅ ↔ β = zero := by
  constructor
  · intro h; funext t
    have : t ∉ occ β := by rw [h]; simp
    simp only [occ, mem_filter, mem_univ, true_and] at this
    simpa [zero, APEX.PXP.zero] using this
  · rintro rfl; exact occ_zero

lemma flips_zero' : flips (zero : Traj k) = ∅ := APEX.PXP.flips_zero
lemma flips_one' : flips (one : Traj k) = ∅ := APEX.PXP.flips_one

lemma occ_nonempty_of_active {β : Traj k} (h : (flips β).Nonempty) : (occ β).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro h'
  rw [occ_eq_empty_iff] at h'
  rw [h', flips_zero'] at h
  simp at h

/-- The active trajectories. -/
def act (k : ℕ) : Finset (Traj k) := univ.filter (fun β : Traj k => (flips β).Nonempty)

lemma sum_split [NeZero k] (f : Traj k → PowerSeries ℤ) :
    ∑ β : Traj k, f β = f zero + f one + ∑ β ∈ act k, f β := by
  rw [← sum_filter_add_sum_filter_not univ (fun β : Traj k => flips β = ∅),
    filter_flips_empty, sum_pair APEX.PXP.zero_ne_one]
  congr 1
  refine sum_congr ?_ (fun _ _ => rfl)
  ext β; simp [act, nonempty_iff_ne_empty]

/-! ### Depth of a state -/

/-- `σ` constrains exactly the first `j` of the next `r` sites. -/
def Dep (r : ℕ) (σ : St k) (j : ℕ) : Prop :=
  (∀ i < j, (σ i).Nonempty) ∧ ∀ i, j ≤ i → i < r → σ i = ∅

lemma dep_zero_free {r : ℕ} {σ : St k} (h : Dep r σ 0) : ∀ i < r, σ i = free i :=
  fun i hi => h.2 i (Nat.zero_le _) hi

lemma dep_step_zero {r : ℕ} {σ : St k} {j : ℕ} (hj : 1 ≤ j) (hjr : j ≤ r) (h : Dep r σ j) :
    Dep r (step r σ zero) (j - 1) := by
  refine ⟨fun i hi => ?_, fun i hi hir => ?_⟩
  · simp only [step, occ_zero, union_empty]
    rw [if_pos (by omega)]; exact h.1 (i + 1) (by omega)
  · simp only [step, occ_zero, union_empty]
    split_ifs with h'
    · exact h.2 (i + 1) (by omega) h'
    · rfl

lemma dep_step_act {r : ℕ} (σ : St k) {β : Traj k} (hβ : (flips β).Nonempty) :
    Dep r (step r σ β) r := by
  refine ⟨fun i _ => ?_, fun i hi hir => absurd hir (by omega)⟩
  obtain ⟨t, ht⟩ := occ_nonempty_of_active hβ
  exact ⟨t, by simp only [step]; exact mem_union_right _ ht⟩

/-! ### Recursions -/

lemma Gs_dep [NeZero k] {r : ℕ} {σ : St k} {j : ℕ} (hj : 1 ≤ j) (h : Dep r σ j)
    (F : Finset (Fin k)) :
    Gs r σ F = Ec F + X * (Gs r (step r σ zero) F + ∑ β ∈ act k,
      (if Disjoint (occ β) (σ 0) ∧ flips β ⊆ F then Gs r (step r σ β) (F \ flips β) else 0)) := by
  rw [Gs_rec, sum_split]
  have h0 : (σ 0).Nonempty := h.1 0 (by omega)
  rw [if_pos ⟨by rw [occ_zero]; exact disjoint_empty_left _, by rw [flips_zero']; exact empty_subset _⟩,
    flips_zero', sdiff_empty]
  rw [if_neg (by
    rintro ⟨hd, -⟩
    rw [occ_one] at hd
    obtain ⟨t, ht⟩ := h0
    exact disjoint_left.1 hd (mem_univ t) ht), add_zero]

lemma Gs_free [NeZero k] {r : ℕ} (F : Finset (Fin k)) :
    Φ r F = Ec F + X * (Φ r F + Gs r (step r free one) F + ∑ β ∈ act k,
      (if flips β ⊆ F then Gs r (step r free β) (F \ flips β) else 0)) := by
  have hd : ∀ β : Traj k, Disjoint (occ β) (free 0) := fun β => disjoint_empty_right _
  have hz : step r free zero = (free : St k) := by
    funext i; simp [step, free, occ_zero]
  rw [Φ]
  conv_lhs => rw [Gs_rec, sum_split]
  rw [if_pos ⟨hd _, by rw [flips_zero']; exact empty_subset _⟩, flips_zero', sdiff_empty,
    if_pos ⟨hd _, by rw [flips_one']; exact empty_subset _⟩, flips_one', sdiff_empty, hz]
  simp only [hd, true_and]

/-- The fully blocked states `U j`. -/
def Ub (j : ℕ) : St k := fun i => if i < j then univ else ∅

lemma Gs_Ub [NeZero k] {r : ℕ} (hr : 0 < r) {j : ℕ} (hj : 1 ≤ j) (hjr : j ≤ r)
    (F : Finset (Fin k)) : Gs r (Ub j) F = Ec F + X * Gs r (Ub (j - 1)) F := by
  rw [Gs_rec, sum_eq_single zero]
  · rw [if_pos ⟨by rw [occ_zero]; exact disjoint_empty_left _, by rw [flips_zero']; exact empty_subset _⟩,
      flips_zero', sdiff_empty]
    congr 2
    apply Gs_congr hr
    intro i hi
    simp only [step, Ub, occ_zero, union_empty]
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro β _ hβ
    rw [if_neg]
    rintro ⟨hd, -⟩
    have : occ β = ∅ := by
      simp only [Ub, if_pos (show 0 < j by omega)] at hd
      exact eq_empty_of_forall_notMem (fun t ht => disjoint_left.1 hd ht (mem_univ t))
    exact hβ ((occ_eq_empty_iff β).1 this)
  · simp

/-- `S_j = 1 + z + … + z^{j-1}`. -/
noncomputable def Sg (j : ℕ) : PowerSeries ℤ := ∑ i ∈ range j, X ^ i

lemma Sg_succ (j : ℕ) : Sg (j + 1) = 1 + X * Sg j := by
  rw [Sg, sum_range_succ', Sg, mul_sum, add_comm, pow_zero]
  congr 1
  exact sum_congr rfl (fun i _ => by ring)

lemma Gs_Ub_all [NeZero k] {r : ℕ} (hr : 0 < r) (F : Finset (Fin k)) :
    ∀ j ≤ r, Gs r (Ub j) F = Ec F * Sg j + X ^ j * Φ r F
  | 0, _ => by
    rw [Sg, sum_range_zero, mul_zero, zero_add, pow_zero, one_mul, Φ]
    apply Gs_congr hr; intro i _; simp [Ub, free]
  | j + 1, hj => by
    rw [Gs_Ub hr (by omega) hj, Nat.add_sub_cancel, Gs_Ub_all hr F j (by omega), Sg_succ]
    ring

/-- **Free-state identity** `Φ · D_r = E·B_r + z·A`. -/
theorem Φ_mul_D [NeZero k] {r : ℕ} (hr : 0 < r) (F : Finset (Fin k)) :
    Φ r F * Dser r = Ec F * ∑ i ∈ range (r + 1), (X : PowerSeries ℤ) ^ i + X * ∑ β ∈ act k,
      (if flips β ⊆ F then Gs r (step r free β) (F \ flips β) else 0) := by
  have h1 := Gs_free (r := r) F
  have h2 : Gs r (step r free one) F = Gs r (Ub r) F := by
    apply Gs_congr hr; intro i hi
    simp [step, Ub, occ_one, hi]
  have h3 := Gs_Ub_all hr F r le_rfl
  have hB : ∑ i ∈ range (r + 1), (X : PowerSeries ℤ) ^ i = 1 + X * Sg r := by
    rw [← Sg, Sg_succ]
  rw [h2, h3] at h1
  rw [hB, Dser]
  linear_combination h1

lemma Gs_dep_empty [NeZero k] {r : ℕ} (hr : 0 < r) :
    ∀ j ≤ r, ∀ σ : St k, Dep r σ j → Gs r σ ∅ = Sg j + X ^ j * Φ r (∅ : Finset (Fin k))
  | 0, _, σ, h => by
    rw [Sg, sum_range_zero, zero_add, pow_zero, one_mul, Φ]
    exact Gs_congr hr ∅ (dep_zero_free h)
  | j + 1, hj, σ, h => by
    rw [Gs_dep (by omega) h, Gs_dep_empty hr j (by omega) _ (dep_step_zero (by omega) hj h)]
    have : ∑ β ∈ act k, (if Disjoint (occ β) (σ 0) ∧ flips β ⊆ ∅ then
        Gs r (step r σ β) (∅ \ flips β) else 0) = 0 := by
      refine sum_eq_zero (fun β hβ => ?_)
      rw [if_neg]
      rintro ⟨-, hs⟩
      obtain ⟨t, ht⟩ := (mem_filter.1 hβ).2
      exact absurd (hs ht) (by simp)
    rw [this, add_zero, Sg_succ, Ec, if_pos rfl]
    ring

/-- After an active site and with no flips left, the series is `1/D_r`. -/
lemma Gs_dep_r_empty [NeZero k] {r : ℕ} (hr : 0 < r) {σ : St k} (h : Dep r σ r) :
    Gs r σ ∅ * Dser r = 1 := by
  rw [Gs_dep_empty hr r le_rfl σ h]
  have hΦ := Φ_mul_D hr (k := k) (r := r) ∅
  have hA : ∑ β ∈ act k, (if flips β ⊆ (∅ : Finset (Fin k)) then
      Gs r (step r free β) (∅ \ flips β) else 0) = 0 := by
    refine sum_eq_zero (fun β hβ => ?_)
    rw [if_neg]
    intro hs
    obtain ⟨t, ht⟩ := (mem_filter.1 hβ).2
    exact absurd (hs ht) (by simp)
  rw [hA, mul_zero, add_zero, Ec, if_pos rfl, one_mul] at hΦ
  have hI := ident_a (X : PowerSeries ℤ) r
  rw [add_mul, mul_assoc, hΦ]
  simp only [Sg, Dser]
  linear_combination hI

/-- Odd or too small flip sets cannot be covered. -/
lemma N_eq_zero_of_card_lt {r : ℕ} {F : Finset (Fin k)} (hF : F ≠ ∅) (h2 : F.card < 2) :
    ∀ (n : ℕ) (σ : St k), N r n σ F = 0
  | 0, σ => by simp [N, hF]
  | n + 1, σ => by
    simp only [N]
    refine sum_eq_zero (fun β _ => ?_)
    split_ifs with h
    · have hc := card_le_card h.2
      have he : flips β = ∅ := by
        by_contra hne
        have := two_le_card_flips (nonempty_iff_ne_empty.2 hne)
        omega
      rw [he, sdiff_empty]
      exact N_eq_zero_of_card_lt hF h2 n _
    · rfl

lemma Gs_eq_zero_of_card_lt {r : ℕ} {F : Finset (Fin k)} (hF : F ≠ ∅) (h2 : F.card < 2)
    (σ : St k) : Gs r σ F = 0 := by
  ext n; simp [Gs, N_eq_zero_of_card_lt hF h2]

/-! ### Degree bookkeeping relative to `D_r` -/

/-- `D_r` as a polynomial. -/
noncomputable def Dpol (r : ℕ) : Polynomial ℤ := 1 - Polynomial.X - Polynomial.X ^ (r + 1)

lemma coe_Dpol (r : ℕ) : ((Dpol r : Polynomial ℤ) : PowerSeries ℤ) = Dser r := by
  simp [Dpol, Dser]

lemma natDegree_Dpol_le (r : ℕ) : (Dpol r).natDegree ≤ r + 1 := by
  unfold Dpol
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · simp
    · have := Polynomial.natDegree_X_le (R := ℤ); omega
  · simp

/-- `Good r S e d` : `S · D_r^e` is a polynomial of degree at most `d`. -/
def Good (r : ℕ) (S : PowerSeries ℤ) (e d : ℕ) : Prop :=
  ∃ p : Polynomial ℤ, p.natDegree ≤ d ∧ S * Dser r ^ e = (p : PowerSeries ℤ)

lemma Good.zero (r e d : ℕ) : Good r 0 e d := ⟨0, by simp, by simp⟩

lemma Good.add {r : ℕ} {S S' : PowerSeries ℤ} {e d : ℕ} (h : Good r S e d) (h' : Good r S' e d) :
    Good r (S + S') e d := by
  obtain ⟨p, hp, hS⟩ := h
  obtain ⟨p', hp', hS'⟩ := h'
  refine ⟨p + p', (Polynomial.natDegree_add_le _ _).trans (max_le hp hp'), ?_⟩
  rw [add_mul, hS, hS', Polynomial.coe_add]

lemma Good.sum {r : ℕ} {ι : Type*} (s : Finset ι) (S : ι → PowerSeries ℤ) {e d : ℕ}
    (h : ∀ i ∈ s, Good r (S i) e d) : Good r (∑ i ∈ s, S i) e d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.zero r e d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma Good.mono {r : ℕ} {S : PowerSeries ℤ} {e d d' : ℕ} (h : Good r S e d) (hd : d ≤ d') :
    Good r S e d' := by
  obtain ⟨p, hp, hS⟩ := h
  exact ⟨p, hp.trans hd, hS⟩

lemma Good.lift {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} (h : Good r S e d) :
    Good r S (e + 1) (d + (r + 1)) := by
  obtain ⟨p, hp, hS⟩ := h
  refine ⟨p * Dpol r, (Polynomial.natDegree_mul_le).trans (add_le_add hp (natDegree_Dpol_le r)), ?_⟩
  rw [pow_succ, ← mul_assoc, hS, Polynomial.coe_mul, coe_Dpol]

lemma Good.lift_many {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} (h : Good r S e d) (j : ℕ) :
    Good r S (e + j) (d + (r + 1) * j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have := ih.lift
    rw [show e + (j + 1) = e + j + 1 by ring, show d + (r + 1) * (j + 1) = d + (r + 1) * j + (r + 1)
      by ring]
    exact this

lemma Good.X_mul {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} (h : Good r S e d) :
    Good r (X * S) e (d + 1) := by
  obtain ⟨p, hp, hS⟩ := h
  refine ⟨Polynomial.X * p, ?_, ?_⟩
  · refine (Polynomial.natDegree_mul_le).trans ?_
    have := Polynomial.natDegree_X_le (R := ℤ)
    omega
  · rw [mul_assoc, hS, Polynomial.coe_mul, Polynomial.coe_X]

lemma Good.div {r : ℕ} {S S' : PowerSeries ℤ} {e d : ℕ} (h : Good r S e d)
    (hS' : S' * Dser r = S) : Good r S' (e + 1) d := by
  obtain ⟨p, hp, hS⟩ := h
  refine ⟨p, hp, ?_⟩
  rw [pow_succ', ← mul_assoc, hS', hS]

lemma Good.ite {r : ℕ} {S : PowerSeries ℤ} {e d : ℕ} (P : Prop) [Decidable P] (h : P → Good r S e d) :
    Good r (if P then S else 0) e d := by
  split_ifs with hp
  · exact h hp
  · exact Good.zero r e d

/-! ### The main induction -/

lemma arith1 (r g g' : ℕ) (h : g' + 1 ≤ g) :
    (2 * r + 1) * (g' + 1) + (r + 1) * (g - (g' + 1)) ≤ (2 * r + 1) * g := by
  obtain ⟨d, rfl⟩ : ∃ d, g = g' + 1 + d := ⟨g - (g' + 1), by omega⟩
  rw [show g' + 1 + d - (g' + 1) = d by omega]
  nlinarith

lemma arith2 (r g : ℕ) : (r + 1) * g ≤ (2 * r + 1) * g := by nlinarith

theorem good_main [NeZero k] {r : ℕ} (hr : 1 ≤ r) :
    ∀ (c : ℕ) (F : Finset (Fin k)), F.card = c → ∀ g : ℕ, c / 2 = g + 1 →
      Good r (Φ r F) (g + 2) ((2 * r + 1) * g + 1) ∧
      ∀ j, 1 ≤ j → j ≤ r → ∀ σ : St k, Dep r σ j →
        Good r (Gs r σ F) (g + 2) ((2 * r + 1) * g + r + 1 + j) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro F hc g hg
  have hF0 : F ≠ ∅ := by
    rintro rfl; simp at hc; omega
  have hE : Ec F = 0 := by simp [Ec, hF0]
  -- active terms
  have hact : ∀ β ∈ act k, flips β ⊆ F → ∀ σ' : St k, Dep r σ' r →
      Good r (Gs r σ' (F \ flips β)) (g + 1) ((2 * r + 1) * g) := by
    intro β hβ hs σ' hσ'
    have h2 := two_le_card_flips (mem_filter.1 hβ).2
    have hcard : (F \ flips β).card = c - (flips β).card := by
      rw [card_sdiff_of_subset hs, hc]
    by_cases he : F \ flips β = ∅
    · rw [he]
      have h1 : Good r (Gs r σ' ∅) 1 0 :=
        ⟨1, by simp, by rw [pow_one, Gs_dep_r_empty (by omega) hσ', Polynomial.coe_one]⟩
      have := h1.lift_many g
      rw [show 1 + g = g + 1 by ring, zero_add] at this
      exact this.mono (arith2 r g)
    · by_cases hlt : (F \ flips β).card < 2
      · rw [Gs_eq_zero_of_card_lt he hlt]; exact Good.zero _ _ _
      · push_neg at hlt
        obtain ⟨g', hg'⟩ : ∃ g', (F \ flips β).card / 2 = g' + 1 := ⟨(F \ flips β).card / 2 - 1, by omega⟩
        have hlt' : (F \ flips β).card < c := by omega
        have hgg : g' + 1 ≤ g := by omega
        have := ((ih _ hlt' (F \ flips β) rfl g' hg').2 r hr le_rfl σ' hσ').lift_many (g - (g' + 1))
        rw [show g' + 2 + (g - (g' + 1)) = g + 1 by omega,
          show (2 * r + 1) * g' + r + 1 + r = (2 * r + 1) * (g' + 1) by ring] at this
        exact this.mono (arith1 r g g' hgg)
  -- free state
  have hΦ : Good r (Φ r F) (g + 2) ((2 * r + 1) * g + 1) := by
    have hm := Φ_mul_D (by omega : 0 < r) F
    rw [hE, zero_mul, zero_add] at hm
    refine Good.div ?_ hm
    refine Good.X_mul (Good.sum _ _ (fun β hβ => Good.ite _ (fun hs => ?_)))
    exact hact β hβ hs _ (dep_step_act free (mem_filter.1 hβ).2)
  refine ⟨hΦ, ?_⟩
  intro j hj1
  induction j with
  | zero => omega
  | succ j ihj =>
    intro hjr σ hσ
    rw [Gs_dep (by omega) hσ, hE, zero_add]
    have hz : Good r (Gs r (step r σ zero) F) (g + 2) ((2 * r + 1) * g + r + 1 + j) := by
      have hd := dep_step_zero (by omega) hjr hσ
      rw [Nat.add_sub_cancel] at hd
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rw [Gs_congr (by omega) F (dep_zero_free hd)]
        exact hΦ.mono (by omega)
      · exact ihj hjpos (by omega) _ hd
    have hs : Good r (∑ β ∈ act k, (if Disjoint (occ β) (σ 0) ∧ flips β ⊆ F then
        Gs r (step r σ β) (F \ flips β) else 0)) (g + 2) ((2 * r + 1) * g + r + 1 + j) := by
      refine Good.sum _ _ (fun β hβ => Good.ite _ (fun hs => ?_))
      have := (hact β hβ hs.2 _ (dep_step_act σ (mem_filter.1 hβ).2)).lift
      exact this.mono (by omega)
    have := (hz.add hs).X_mul
    rwa [show (2 * r + 1) * g + r + 1 + j + 1 = (2 * r + 1) * g + r + 1 + (j + 1) by ring] at this

/-- **Rationality of the transfer series** at the full flip set `F = univ`, `k = 2m`. -/
theorem good_free_univ {r : ℕ} (hr : 1 ≤ r) {m : ℕ} (hm : 1 ≤ m) :
    Good r (Φ r (univ : Finset (Fin (2 * m)))) (m + 1) ((2 * r + 1) * (m - 1) + 1) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have := (good_main hr (2 * m) (univ : Finset (Fin (2 * m))) (by rw [card_univ, Fintype.card_fin])
    (m - 1) (by omega)).1
  rwa [show m - 1 + 2 = m + 1 by omega] at this

end APEX.Blockade.General
