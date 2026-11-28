import APEX.Blockade.General.Transfer

/-!
# Range-`r` blockade: closed walks = trajectory arrays = transfer counts

* `N_eq_cnt` : the transfer count `N r n σ F` counts arrays `a : Fin n → Traj k` with pairwise
  disjoint flip sets of union `F`, the range-`r` blockade between sites at distance `≤ r`, and the
  initial constraints `σ`.
* `trace_eq_N` : `Tr (adjMat r n)^k = N r n free univ` (`k ≥ 1`, `r ≥ 1`).
-/

namespace APEX.Blockade.General

open Finset
open APEX.PXP (Traj flips mem_flips Compat PD U disj_union_iff one_flip_iff)

variable {k : ℕ}

/-- Range-`r` blockade inside an array. -/
def Blk (r : ℕ) {n : ℕ} (a : Fin n → Traj k) : Prop :=
  ∀ i j : Fin n, i < j → j.val ≤ i.val + r → Compat (a i) (a j)

/-- Initial constraints. -/
def CS (r : ℕ) (σ : St k) {n : ℕ} (a : Fin n → Traj k) : Prop :=
  ∀ i : Fin n, i.val < r → Disjoint (occ (a i)) (σ i.val)

instance (r : ℕ) {n : ℕ} (a : Fin n → Traj k) : Decidable (Blk r a) := by
  unfold Blk; infer_instance
instance (r : ℕ) (σ : St k) {n : ℕ} (a : Fin n → Traj k) : Decidable (CS r σ a) := by
  unfold CS; infer_instance
instance {n : ℕ} (a : Fin n → Traj k) : Decidable (PD a) := by unfold PD; infer_instance

/-- Array count. -/
def cnt (r n : ℕ) (σ : St k) (F : Finset (Fin k)) : ℕ :=
  ∑ a : Fin n → Traj k, if PD a ∧ U a = F ∧ Blk r a ∧ CS r σ a then 1 else 0

lemma compat_iff (β γ : Traj k) : Compat β γ ↔ Disjoint (occ β) (occ γ) := by
  unfold Compat occ
  rw [disjoint_left]
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h t h1 h2; exact h t ⟨h1, h2⟩
  · rintro h t ⟨h1, h2⟩; exact h h1 h2

lemma sum_cons {n : ℕ} (f : (Fin (n + 1) → Traj k) → ℕ) :
    ∑ a : Fin (n + 1) → Traj k, f a = ∑ β : Traj k, ∑ b : Fin n → Traj k, f (Fin.cons β b) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Traj k)) _ _ (fun p => rfl)).symm

lemma PD_cons {n : ℕ} (β : Traj k) (b : Fin n → Traj k) :
    PD (Fin.cons β b : Fin (n + 1) → Traj k) ↔ PD b ∧ Disjoint (U b) (flips β) := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ?_⟩
    · have := h i.succ j.succ (fun e => hij (Fin.succ_injective _ e))
      simpa only [Fin.cons_succ] using this
    · rw [U, disjoint_biUnion_left]
      intro i _
      have := h i.succ 0 (Fin.succ_ne_zero i)
      simpa only [Fin.cons_succ, Fin.cons_zero] using this
  · rintro ⟨hb, hx⟩ i j hij
    have hx' : ∀ i, Disjoint (flips (b i)) (flips β) := by
      intro i
      rw [U, disjoint_biUnion_left] at hx
      exact hx i (mem_univ _)
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => rw [Fin.cons_zero, Fin.cons_succ]; exact (hx' j).symm
    | succ i =>
      induction j using Fin.cases with
      | zero => rw [Fin.cons_zero, Fin.cons_succ]; exact hx' i
      | succ j =>
        rw [Fin.cons_succ, Fin.cons_succ]
        exact hb i j (fun e => hij (by rw [e]))

lemma U_cons {n : ℕ} (β : Traj k) (b : Fin n → Traj k) :
    U (Fin.cons β b : Fin (n + 1) → Traj k) = U b ∪ flips β := by
  ext t
  simp only [U, mem_biUnion, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.cases with
    | zero => rw [Fin.cons_zero] at hi; exact Or.inr hi
    | succ i => rw [Fin.cons_succ] at hi; exact Or.inl ⟨i, hi⟩
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.succ, by rw [Fin.cons_succ]; exact hi⟩
    · exact ⟨0, by rw [Fin.cons_zero]; exact hi⟩

lemma Blk_cons (r : ℕ) {n : ℕ} (β : Traj k) (b : Fin n → Traj k) :
    Blk r (Fin.cons β b : Fin (n + 1) → Traj k) ↔
      (∀ j : Fin n, j.val < r → Compat β (b j)) ∧ Blk r b := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun i j hij hr => ?_⟩
    · have := h 0 j.succ (Fin.succ_pos j) (by simp; omega)
      simpa only [Fin.cons_zero, Fin.cons_succ] using this
    · have := h i.succ j.succ (Fin.succ_lt_succ_iff.2 hij) (by simp; omega)
      simpa only [Fin.cons_succ] using this
  · rintro ⟨h1, h2⟩ i j hij hr
    induction j using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero i)
    | succ j =>
      induction i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero, Fin.cons_succ]
        exact h1 j (by simp at hr; omega)
      | succ i =>
        rw [Fin.cons_succ, Fin.cons_succ]
        exact h2 i j (Fin.succ_lt_succ_iff.1 hij) (by simp at hr; omega)

lemma cond_cons {r : ℕ} (hr : 0 < r) {n : ℕ} (σ : St k) (F : Finset (Fin k)) (β : Traj k)
    (b : Fin n → Traj k) :
    (PD (Fin.cons β b : Fin (n + 1) → Traj k) ∧ U (Fin.cons β b : Fin (n + 1) → Traj k) = F ∧
      Blk r (Fin.cons β b : Fin (n + 1) → Traj k) ∧ CS r σ (Fin.cons β b : Fin (n + 1) → Traj k)) ↔
    ((Disjoint (occ β) (σ 0) ∧ flips β ⊆ F) ∧
      (PD b ∧ U b = F \ flips β ∧ Blk r b ∧ CS r (step r σ β) b)) := by
  rw [PD_cons, U_cons, Blk_cons]
  have hCS : CS r σ (Fin.cons β b : Fin (n + 1) → Traj k) ↔
      Disjoint (occ β) (σ 0) ∧ ∀ j : Fin n, j.val + 1 < r → Disjoint (occ (b j)) (σ (j.val + 1)) := by
    constructor
    · intro h
      refine ⟨by simpa using h 0 hr, fun j hj => ?_⟩
      have := h j.succ (by simp; omega)
      simpa only [Fin.cons_succ, Fin.val_succ] using this
    · rintro ⟨h1, h2⟩ i hi
      induction i using Fin.cases with
      | zero => simpa using h1
      | succ i => rw [Fin.cons_succ, Fin.val_succ]; exact h2 i (by simp at hi; omega)
  have hstep : CS r (step r σ β) b ↔ (∀ j : Fin n, j.val < r → Disjoint (occ (b j)) (occ β)) ∧
      ∀ j : Fin n, j.val + 1 < r → Disjoint (occ (b j)) (σ (j.val + 1)) := by
    unfold CS step
    constructor
    · intro h
      refine ⟨fun j hj => (disjoint_union_right.1 (h j hj)).2, fun j hj => ?_⟩
      have := (disjoint_union_right.1 (h j (by omega))).1
      rwa [if_pos hj] at this
    · rintro ⟨h1, h2⟩ j hj
      refine disjoint_union_right.2 ⟨?_, h1 j hj⟩
      split_ifs with h
      · exact h2 j h
      · exact disjoint_empty_right _
  rw [hCS, hstep]
  have hdu := disj_union_iff (U b) (flips β) F
  have hc : (∀ j : Fin n, j.val < r → Compat β (b j)) ↔
      (∀ j : Fin n, j.val < r → Disjoint (occ (b j)) (occ β)) := by
    refine forall_congr' (fun j => imp_congr_right (fun _ => ?_))
    rw [compat_iff, disjoint_comm]
  rw [hc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, ⟨h4, h5⟩, h6, h7⟩
    have := hdu.1 ⟨h2, h3⟩
    exact ⟨⟨h6, this.1⟩, h1, this.2, h5, h4, h7⟩
  · rintro ⟨⟨h6, hs⟩, h1, hU, h5, h4, h7⟩
    have := hdu.2 ⟨hs, hU⟩
    exact ⟨⟨h1, this.1⟩, this.2, ⟨h4, h5⟩, h6, h7⟩

theorem N_eq_cnt {r : ℕ} (hr : 0 < r) : ∀ (n : ℕ) (σ : St k) (F : Finset (Fin k)),
    N r n σ F = cnt r n σ F
  | 0, σ, F => by
    unfold cnt
    rw [Fintype.sum_unique]
    have hPD : ∀ a : Fin 0 → Traj k, PD a := fun a i => i.elim0
    have hU : ∀ a : Fin 0 → Traj k, U a = ∅ := fun a => by simp [U]
    have hB : ∀ a : Fin 0 → Traj k, Blk r a := fun a i => i.elim0
    have hC : ∀ a : Fin 0 → Traj k, CS r σ a := fun a i => i.elim0
    simp only [N]
    by_cases h : F = ∅
    · rw [if_pos h, if_pos ⟨hPD _, by rw [hU, h], hB _, hC _⟩]
    · rw [if_neg h, if_neg (fun h' => h (by rw [← h'.2.1, hU]))]
  | n + 1, σ, F => by
    unfold cnt
    rw [sum_cons]
    simp only [N]
    refine sum_congr rfl (fun β _ => ?_)
    simp_rw [cond_cons hr σ F β]
    rw [N_eq_cnt hr n, cnt]
    split_ifs with h
    · refine sum_congr rfl (fun b _ => ?_)
      simp only [h, true_and]
    · symm
      refine sum_eq_zero (fun b _ => ?_)
      rw [if_neg (fun h' => h h'.1)]

/-! ### Closed walks -/

lemma adj_iff_card {r n : ℕ} (u v : V r n) :
    Adj u.1 v.1 ↔ (univ.filter (fun j : Fin n => v.1.getD j false ≠ u.1.getD j false)).card = 1 := by
  have hu := (mem_C.1 u.2).1
  have hv := (mem_C.1 v.2).1
  constructor
  · rintro ⟨i, hi, hv'⟩
    rw [mem_range] at hi
    rw [card_eq_one]
    refine ⟨⟨i, by omega⟩, ?_⟩
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    rw [hv', getD_flip (by omega)]
    constructor
    · intro h
      ext
      by_contra hc
      rw [if_neg hc] at h
      exact h rfl
    · intro h
      rw [h, if_pos rfl]
      cases u.1.getD i false <;> simp
  · intro h
    obtain ⟨i, hi⟩ := card_eq_one.1 h
    refine ⟨i.val, by rw [mem_range]; omega, ?_⟩
    apply ext_getD (by rw [length_flip]; omega)
    intro t
    rw [getD_flip (by omega)]
    rcases Nat.lt_or_ge t n with ht | ht
    · have hm : (⟨t, ht⟩ : Fin n) ∈ univ.filter
          (fun j : Fin n => v.1.getD j false ≠ u.1.getD j false) ↔ (⟨t, ht⟩ : Fin n) = i := by
        rw [hi, mem_singleton]
      simp only [mem_filter, mem_univ, true_and] at hm
      split_ifs with hti
      · subst hti
        have := hm.2 (by ext; rfl)
        cases hx : v.1.getD i.val false <;> cases hy : u.1.getD i.val false <;> simp_all
      · by_contra hc
        exact hti (congrArg Fin.val (hm.1 hc))
    · rw [if_neg (by omega)]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

lemma getD_ofFn {n : ℕ} (f : Fin n → Bool) (j : Fin n) : (List.ofFn f).getD j false = f j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos j.2]
  rfl

theorem trace_eq_N {r : ℕ} (hr : 1 ≤ r) (n : ℕ) [NeZero k] :
    Matrix.trace (adjMat r n ^ k) = (N r n free (univ : Finset (Fin k)) : ℤ) := by
  have hM : adjMat r n = APEX.PXP.relMat (fun u v : V r n => Adj u.1 v.1) := rfl
  rw [hM, APEX.PXP.trace_relMat_pow, N_eq_cnt (by omega), cnt]
  push_cast
  rw [← sum_filter, ← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  congr 1
  refine card_bij (fun c _ => fun j t => (c t).1.getD j false) ?_ ?_ ?_
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    have h1 := (one_flip_iff (k := k) (fun j t => (c t).1.getD j false)).1 (fun t =>
      (adj_iff_card (c t) (c (finRotate k t))).1 (hc t))
    refine ⟨h1.1, h1.2, fun i j hij hjr t => ?_, fun i _ => disjoint_empty_right _⟩
    have hI := (adm_iff r _).1 (mem_C.1 (c t).2).2
    rintro ⟨h1, h2⟩
    have := hI i j hij hjr h1
    simp_all
  · intro c _ c' _ h
    funext t
    apply Subtype.ext
    apply ext_getD (by rw [(mem_C.1 (c t).2).1, (mem_C.1 (c' t).2).1])
    intro j
    rcases Nat.lt_or_ge j n with hj | hj
    · exact congrFun (congrFun h ⟨j, hj⟩) t
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [(mem_C.1 (c t).2).1]; omega),
        List.getElem?_eq_none (by rw [(mem_C.1 (c' t).2).1]; omega)]
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    obtain ⟨hPD, hU, hB, -⟩ := ha
    have hmem : ∀ t, List.ofFn (fun j : Fin n => a j t) ∈ C r n := by
      intro t
      rw [mem_C]
      refine ⟨List.length_ofFn, (adm_iff r _).2 (fun s s' hss hsr hs => ?_)⟩
      rcases Nat.lt_or_ge s' n with h' | h'
      · have h1 : (List.ofFn (fun j : Fin n => a j t)).getD s false = a ⟨s, by omega⟩ t :=
          getD_ofFn (fun j : Fin n => a j t) ⟨s, by omega⟩
        have h2 : (List.ofFn (fun j : Fin n => a j t)).getD s' false = a ⟨s', h'⟩ t :=
          getD_ofFn (fun j : Fin n => a j t) ⟨s', h'⟩
        rw [h1] at hs
        rw [h2]
        have := hB ⟨s, by omega⟩ ⟨s', h'⟩ (Fin.mk_lt_mk.2 hss) hsr t
        cases hx : a ⟨s', h'⟩ t <;> simp_all
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
    refine ⟨fun t => ⟨List.ofFn (fun j : Fin n => a j t), hmem t⟩, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      intro t
      have := (one_flip_iff a).2 ⟨hPD, hU⟩ t
      exact (adj_iff_card (⟨_, hmem t⟩ : V r n) ⟨_, hmem (finRotate k t)⟩).2
        (by simp only [getD_ofFn]; exact this)
    · funext j t
      exact getD_ofFn (fun j : Fin n => a j t) j

end APEX.Blockade.General
