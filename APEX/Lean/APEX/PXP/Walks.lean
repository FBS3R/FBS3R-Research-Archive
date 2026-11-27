/-
# From the adjacency matrix of the Fibonacci cube to trajectory arrays

* `relMat_pow_apply` / `trace_relMat_pow` : powers of a 0/1 matrix count walks, and the trace of
  the `k`-th power counts cyclic closed walks `Fin k → α`;
* `Cfg n`, `adjMat n` : legal configurations of the open chain and the adjacency matrix of the
  Fibonacci cube `Γₙ` — the open-chain PXP Hamiltonian with unit couplings and zero field;
* `card_walks_eq_card_arrays` : closed walks ↔ admissible trajectory arrays;
* `g_succ_eq_count` : the transfer recursion `g` counts admissible arrays.
-/
import APEX.PXP.Rational
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace APEX.PXP

open Finset

/-! ### Generic: matrix powers of a 0/1 matrix count walks -/

section Generic

variable {α : Type*} [Fintype α] [DecidableEq α] (R : α → α → Prop) [DecidableRel R]

/-- The 0/1 matrix of a relation. -/
def relMat : Matrix α α ℤ := Matrix.of fun a b => if R a b then 1 else 0

/-- Steps of a walk `w : Fin (k+1) → α`. -/
def Steps {k : ℕ} (w : Fin (k + 1) → α) : Prop := ∀ t : Fin k, R (w t.castSucc) (w t.succ)

instance {k : ℕ} (w : Fin (k + 1) → α) : Decidable (Steps R w) := by
  unfold Steps; infer_instance

/-- Number of walks with `k` steps from `i` to `j`. -/
def walkCount (k : ℕ) (i j : α) : ℤ :=
  ∑ w : Fin (k + 1) → α, if w 0 = i ∧ w (Fin.last k) = j ∧ Steps R w then 1 else 0

lemma sum_snoc {β : Type*} [AddCommMonoid β] {n : ℕ} (f : (Fin (n + 1) → α) → β) :
    ∑ w : Fin (n + 1) → α, f w = ∑ x : α, ∑ v : Fin n → α, f (Fin.snoc v x) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ => α)) _ _ (fun p => rfl)).symm

lemma steps_snoc {k : ℕ} (v : Fin (k + 1) → α) (x : α) :
    Steps R (Fin.snoc v x : Fin (k + 2) → α) ↔ Steps R v ∧ R (v (Fin.last k)) x := by
  unfold Steps
  rw [Fin.forall_fin_succ']
  apply and_congr
  · apply forall_congr'
    intro t
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]

lemma snoc_zero' {k : ℕ} (v : Fin (k + 1) → α) (x : α) :
    (Fin.snoc v x : Fin (k + 2) → α) 0 = v 0 := by
  rw [← Fin.castSucc_zero, Fin.snoc_castSucc]

lemma relMat_pow_apply (k : ℕ) (i j : α) : (relMat R ^ k) i j = walkCount R k i j := by
  induction k generalizing j with
  | zero =>
    simp only [pow_zero, walkCount]
    rw [Matrix.one_apply, Finset.sum_eq_single (fun _ => i)]
    · by_cases h : i = j
      · subst h; simp [Steps]
      · simp [h]
    · intro w _ hw
      rw [if_neg]
      rintro ⟨h0, -, -⟩
      exact hw (funext fun t => by rw [Fin.fin_one_eq_zero t, h0])
    · simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih]
    unfold walkCount
    -- left side
    have hL : ∑ l : α, (∑ w : Fin (k + 1) → α,
        if w 0 = i ∧ w (Fin.last k) = l ∧ Steps R w then (1 : ℤ) else 0) * relMat R l j =
        ∑ v : Fin (k + 1) → α, if v 0 = i ∧ Steps R v ∧ R (v (Fin.last k)) j then 1 else 0 := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.sum_eq_single (v (Fin.last k))]
      · simp only [relMat, Matrix.of_apply, true_and]
        by_cases h1 : v 0 = i <;> by_cases h2 : Steps R v <;> by_cases h3 : R (v (Fin.last k)) j <;>
          simp [h1, h2, h3]
      · intro l _ hl
        simp [Ne.symm hl]
      · simp
    rw [hL, sum_snoc (α := α) (n := k + 1), Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      refine if_congr ?_ rfl rfl
      rw [snoc_zero', Fin.snoc_last, steps_snoc]
      simp only [true_and]
    · intro x _ hx
      refine Finset.sum_eq_zero (fun v _ => ?_)
      rw [Fin.snoc_last, if_neg]
      rintro ⟨-, h, -⟩
      exact hx h
    · simp

lemma rotate_succ_eq {k : ℕ} (c : Fin (k + 1) → α) (t : Fin (k + 1)) :
    (Fin.snoc c (c 0) : Fin (k + 2) → α) t.succ = c (finRotate (k + 1) t) := by
  by_cases ht : t = Fin.last k
  · subst ht
    rw [Fin.succ_last, Fin.snoc_last, finRotate_last]
  · have hlt : (t : ℕ) < k := by
      have := Fin.val_lt_last ht
      simpa using this
    have h1 : t.succ = Fin.castSucc ⟨t + 1, by omega⟩ := by ext; simp
    have h2 : finRotate (k + 1) t = ⟨t + 1, by omega⟩ := by
      ext; rw [coe_finRotate, if_neg ht]
    rw [h1, Fin.snoc_castSucc, h2]

/-- The trace of the `k`-th power counts cyclic closed walks. -/
theorem trace_relMat_pow (k : ℕ) [NeZero k] :
    Matrix.trace (relMat R ^ k) =
      ∑ c : Fin k → α, if ∀ t, R (c t) (c (finRotate k t)) then 1 else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := NeZero.ne k; omega⟩
  unfold Matrix.trace
  simp only [Matrix.diag_apply, relMat_pow_apply, walkCount]
  rw [Finset.sum_comm]
  rw [sum_snoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_eq_single (c 0)]
  · rw [Finset.sum_eq_single (c 0)]
    · rw [Fin.snoc_last, snoc_zero']
      simp only [true_and]
      congr 1
      apply propext
      unfold Steps
      apply forall_congr'
      intro t
      rw [Fin.snoc_castSucc, rotate_succ_eq]
    · intro i _ hi
      rw [if_neg]
      rintro ⟨h0, -, -⟩
      rw [snoc_zero'] at h0
      exact hi h0.symm
    · simp
  · intro x _ hx
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_neg]
    rintro ⟨h0, h1, -⟩
    rw [snoc_zero'] at h0
    rw [Fin.snoc_last] at h1
    exact hx (h1.trans h0.symm)
  · simp

end Generic

/-! ### The Fibonacci cube -/

/-- Legal configurations: no two adjacent occupied sites. -/
def Legal {n : ℕ} (s : Fin n → Bool) : Prop :=
  ∀ i : Fin n, ∀ h : i.val + 1 < n, ¬ (s i = true ∧ s ⟨i.val + 1, h⟩ = true)

instance {n : ℕ} (s : Fin n → Bool) : Decidable (Legal s) := by unfold Legal; infer_instance

/-- The constrained Hilbert-space basis `𝒞ₙ`. -/
abbrev Cfg (n : ℕ) := {s : Fin n → Bool // Legal s}

/-- Fibonacci-cube adjacency: the two configurations differ at exactly one site. -/
def Adj {n : ℕ} (s s' : Cfg n) : Prop := (univ.filter (fun j => s.1 j ≠ s'.1 j)).card = 1

instance {n : ℕ} : DecidableRel (Adj (n := n)) := fun _ _ => by unfold Adj; infer_instance

/-- The adjacency matrix `Aₙ` of the Fibonacci cube = open PXP chain, unit couplings, no field. -/
def adjMat (n : ℕ) : Matrix (Cfg n) (Cfg n) ℤ := relMat (Adj (n := n))

variable {k : ℕ}

/-! ### Admissible trajectory arrays -/

/-- Pairwise disjoint flip sets. -/
def PD {n : ℕ} (a : Fin n → Traj k) : Prop := ∀ i j, i ≠ j → Disjoint (flips (a i)) (flips (a j))

/-- Blockade between neighbouring sites at every time. -/
def CC {n : ℕ} (a : Fin n → Traj k) : Prop :=
  ∀ i : Fin n, ∀ h : i.val + 1 < n, Compat (a i) (a ⟨i.val + 1, h⟩)

/-- Union of the flip sets. -/
def U {n : ℕ} (a : Fin n → Traj k) : Finset (Fin k) := univ.biUnion (fun i => flips (a i))

instance {n : ℕ} (a : Fin n → Traj k) : Decidable (PD a) := by unfold PD; infer_instance
instance {n : ℕ} (a : Fin n → Traj k) : Decidable (CC a) := by unfold CC; infer_instance

lemma PD_snoc {n : ℕ} (b : Fin (n + 1) → Traj k) (x : Traj k) :
    PD (Fin.snoc b x : Fin (n + 2) → Traj k) ↔ PD b ∧ Disjoint (U b) (flips x) := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ?_⟩
    · have := h i.castSucc j.castSucc (fun e => hij (Fin.castSucc_injective _ e))
      simpa only [Fin.snoc_castSucc] using this
    · rw [U, Finset.disjoint_biUnion_left]
      intro i _
      have := h i.castSucc (Fin.last _) (Fin.castSucc_lt_last i).ne
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using this
  · rintro ⟨hb, hx⟩ i j hij
    have hx' : ∀ i, Disjoint (flips (b i)) (flips x) := by
      intro i
      rw [U, Finset.disjoint_biUnion_left] at hx
      exact hx i (mem_univ _)
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j => rw [Fin.snoc_last, Fin.snoc_castSucc]; exact (hx' j).symm
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.snoc_castSucc]; exact hx' i
      | cast j =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hb i j (fun e => hij (by rw [e]))

lemma CC_snoc {n : ℕ} (b : Fin (n + 1) → Traj k) (x : Traj k) :
    CC (Fin.snoc b x : Fin (n + 2) → Traj k) ↔ CC b ∧ Compat (b (Fin.last n)) x := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have := h i.castSucc (by simp; omega)
      have e : (⟨i.castSucc.val + 1, by simp; omega⟩ : Fin (n + 2)) = Fin.castSucc ⟨i.val + 1, hi⟩ :=
        by ext; simp
      rw [e, Fin.snoc_castSucc, Fin.snoc_castSucc] at this
      exact this
    · have := h (Fin.last n).castSucc (by simp)
      have e : (⟨(Fin.last n).castSucc.val + 1, by simp⟩ : Fin (n + 2)) = Fin.last (n + 1) :=
        by ext; simp
      rw [e, Fin.snoc_castSucc, Fin.snoc_last] at this
      exact this
  · rintro ⟨hb, hx⟩ i hi
    by_cases hlt : i.val + 1 < n + 1
    · have e1 : i = Fin.castSucc ⟨i.val, by omega⟩ := by ext; simp
      have e2 : (⟨i.val + 1, hi⟩ : Fin (n + 2)) = Fin.castSucc ⟨i.val + 1, hlt⟩ := by ext; simp
      rw [e2, Fin.snoc_castSucc]
      conv => arg 1; rw [e1]
      rw [Fin.snoc_castSucc]
      exact hb ⟨i.val, by omega⟩ hlt
    · have e1 : i = Fin.castSucc (Fin.last n) := by ext; simp; omega
      have e2 : (⟨i.val + 1, hi⟩ : Fin (n + 2)) = Fin.last (n + 1) := by ext; simp; omega
      rw [e2, Fin.snoc_last]
      conv => arg 1; rw [e1]
      rw [Fin.snoc_castSucc]
      exact hx

lemma U_snoc {n : ℕ} (b : Fin (n + 1) → Traj k) (x : Traj k) :
    U (Fin.snoc b x : Fin (n + 2) → Traj k) = U b ∪ flips x := by
  ext t
  simp only [U, mem_biUnion, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last] at hi; exact Or.inr hi
    | cast i => rw [Fin.snoc_castSucc] at hi; exact Or.inl ⟨i, hi⟩
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, by rw [Fin.snoc_castSucc]; exact hi⟩
    · exact ⟨Fin.last _, by rw [Fin.snoc_last]; exact hi⟩

/-- Number of admissible arrays of length `n+1` with total flip set `F` ending in `β`. -/
def count (n : ℕ) (β : Traj k) (F : Finset (Fin k)) : ℕ :=
  ∑ a : Fin (n + 1) → Traj k,
    if PD a ∧ CC a ∧ U a = F ∧ a (Fin.last n) = β then 1 else 0

lemma disj_union_iff (S f F : Finset (Fin k)) :
    (Disjoint S f ∧ S ∪ f = F) ↔ (f ⊆ F ∧ S = F \ f) := by
  constructor
  · rintro ⟨hd, rfl⟩
    refine ⟨Finset.subset_union_right, ?_⟩
    rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hd]
  · rintro ⟨hs, rfl⟩
    exact ⟨Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hs⟩

theorem g_succ_eq_count : ∀ (n : ℕ) (β : Traj k) (F : Finset (Fin k)), g (n + 1) β F = count n β F
  | 0, β, F => by
    unfold count
    rw [Finset.sum_eq_single (fun _ => β)]
    · simp only [g, δ, true_and, ite_self, Finset.sum_const_zero, add_zero]
      have hPD : PD (fun _ : Fin 1 => β) := fun i j hij => absurd (Subsingleton.elim i j) hij
      have hCC : CC (fun _ : Fin 1 => β) := fun i hi => by omega
      have hU : U (fun _ : Fin 1 => β) = flips β := by simp [U]
      simp only [hPD, hCC, hU, true_and, and_true]
      by_cases h : flips β ⊆ F
      · rw [if_pos h]
        by_cases h' : F \ flips β = ∅
        · rw [if_pos h', if_pos]
          exact Finset.Subset.antisymm h (Finset.sdiff_eq_empty_iff_subset.1 h')
        · rw [if_neg h', if_neg]
          rintro rfl; simp at h'
      · rw [if_neg h, if_neg]
        rintro rfl; exact h (Finset.Subset.refl _)
    · intro a _ ha
      rw [if_neg]
      rintro ⟨-, -, -, hl⟩
      exact ha (funext fun t => by rw [Fin.fin_one_eq_zero t]; exact hl)
    · simp
  | n + 1, β', F' => by
    have ih := g_succ_eq_count n
    have hR : count (n + 1) β' F' = ∑ v : Fin (n + 1) → Traj k,
        if (PD v ∧ Disjoint (U v) (flips β')) ∧ (CC v ∧ Compat (v (Fin.last n)) β') ∧
          U v ∪ flips β' = F' then 1 else 0 := by
      unfold count
      rw [sum_snoc (α := Traj k) (n := n + 1), Finset.sum_eq_single β']
      · refine Finset.sum_congr rfl (fun v _ => ?_)
        refine if_congr ?_ rfl rfl
        rw [PD_snoc, CC_snoc, U_snoc, Fin.snoc_last]
        simp only [and_true]
      · intro x _ hx
        refine Finset.sum_eq_zero (fun v _ => ?_)
        rw [Fin.snoc_last, if_neg]
        rintro ⟨-, -, -, h⟩
        exact hx h
      · simp
    rw [hR, g]
    have hδ : δ (n + 1) (F' \ flips β') = 0 := by simp [δ]
    by_cases hs : flips β' ⊆ F'
    · rw [if_pos hs, hδ, zero_add]
      simp_rw [ih]
      unfold count
      have e1 : ∀ β : Traj k, (if Compat β β' then ∑ a : Fin (n + 1) → Traj k,
          (if PD a ∧ CC a ∧ U a = F' \ flips β' ∧ a (Fin.last n) = β then 1 else 0) else 0) =
          ∑ a : Fin (n + 1) → Traj k, (if Compat β β' ∧ PD a ∧ CC a ∧ U a = F' \ flips β' ∧
            a (Fin.last n) = β then 1 else 0) := by
        intro β
        split_ifs with hc
        · simp [hc]
        · simp [hc]
      simp_rw [e1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.sum_eq_single (v (Fin.last n))]
      · have key : (PD v ∧ Disjoint (U v) (flips β')) ∧ (CC v ∧ Compat (v (Fin.last n)) β') ∧
            U v ∪ flips β' = F' ↔
            Compat (v (Fin.last n)) β' ∧ PD v ∧ CC v ∧ U v = F' \ flips β' ∧
              v (Fin.last n) = v (Fin.last n) := by
          have := disj_union_iff (U v) (flips β') F'
          constructor
          · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
            exact ⟨h4, h1, h3, (this.1 ⟨h2, h5⟩).2, rfl⟩
          · rintro ⟨h4, h1, h3, h5, -⟩
            have := this.2 ⟨hs, h5⟩
            exact ⟨⟨h1, this.1⟩, ⟨h3, h4⟩, this.2⟩
        push_cast
        simp only [key]
      · intro β _ hβ
        rw [if_neg]
        rintro ⟨-, -, -, -, h⟩
        exact hβ h.symm
      · simp
    · rw [if_neg hs]
      push_cast
      symm
      refine Finset.sum_eq_zero (fun v _ => ?_)
      rw [if_neg]
      rintro ⟨⟨-, h2⟩, -, h5⟩
      exact hs ((disj_union_iff _ _ _).1 ⟨h2, h5⟩).1

/-! ### Closed walks ↔ arrays -/

/-- Exactly-one-flip-per-time ↔ pairwise disjoint flip sets covering all times. -/
lemma one_flip_iff {n : ℕ} (a : Fin n → Traj k) :
    (∀ t : Fin k, (univ.filter (fun j => a j (finRotate k t) ≠ a j t)).card = 1) ↔
      PD a ∧ U a = univ := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro t hi hj
      have h1 := h t
      rw [Finset.card_eq_one] at h1
      obtain ⟨l, hl⟩ := h1
      have hi' : i ∈ univ.filter (fun j => a j (finRotate k t) ≠ a j t) := by
        simpa using mem_flips.1 hi
      have hj' : j ∈ univ.filter (fun j => a j (finRotate k t) ≠ a j t) := by
        simpa using mem_flips.1 hj
      rw [hl, Finset.mem_singleton] at hi' hj'
      exact hij (hi'.trans hj'.symm)
    · refine Finset.eq_univ_of_forall (fun t => ?_)
      have h1 := h t
      rw [Finset.card_eq_one] at h1
      obtain ⟨l, hl⟩ := h1
      have : l ∈ univ.filter (fun j => a j (finRotate k t) ≠ a j t) := by
        rw [hl]; exact Finset.mem_singleton_self l
      simp only [U, mem_biUnion, mem_univ, true_and]
      exact ⟨l, mem_flips.2 (by simpa using this)⟩
  · rintro ⟨hPD, hU⟩ t
    have ht : t ∈ U a := by rw [hU]; exact mem_univ t
    simp only [U, mem_biUnion, mem_univ, true_and] at ht
    obtain ⟨l, hl⟩ := ht
    rw [Finset.card_eq_one]
    refine ⟨l, Finset.eq_singleton_iff_unique_mem.2 ⟨by simpa using mem_flips.1 hl, ?_⟩⟩
    intro j hj
    by_contra hjl
    have hj' : t ∈ flips (a j) := mem_flips.2 (by simpa using hj)
    exact Finset.disjoint_left.1 (hPD j l hjl) hj' hl

lemma legal_iff_CC {n : ℕ} (a : Fin n → Traj k) :
    (∀ t : Fin k, Legal (fun j => a j t)) ↔ CC a := by
  constructor
  · intro h i hi t ht
    exact h t i hi ht
  · intro h t i hi ht
    exact h i hi t ht

/-- Number of cyclic closed walks of length `k` on `Γₙ` equals the number of admissible arrays
covering all times. -/
theorem card_walks_eq_card_arrays (n : ℕ) :
    (∑ c : Fin k → Cfg n, if ∀ t, Adj (c t) (c (finRotate k t)) then (1 : ℤ) else 0) =
      ∑ a : Fin n → Traj k, if PD a ∧ CC a ∧ U a = univ then 1 else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  refine Finset.card_bij (fun c _ => fun j t => (c t).1 j) ?_ ?_ ?_
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    have h1 := (one_flip_iff (k := k) (fun j t => (c t).1 j)).1 (fun t => by
      have := hc t; unfold Adj at this; simpa [ne_comm] using this)
    exact ⟨h1.1, (legal_iff_CC (fun j t => (c t).1 j)).1 (fun t => (c t).2), h1.2⟩
  · intro c _ c' _ h
    funext t
    apply Subtype.ext
    funext j
    exact congrFun (congrFun h j) t
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    have hL := (legal_iff_CC a).2 ha.2.1
    refine ⟨fun t => ⟨fun j => a j t, hL t⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    have := (one_flip_iff a).2 ⟨ha.1, ha.2.2⟩
    intro t; unfold Adj; simpa [ne_comm] using this t

end APEX.PXP
