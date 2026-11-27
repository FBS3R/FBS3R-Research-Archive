/-
# Angular-channel rank count (2026-09-11)

Source: *Field Reconstruction and Curvature Identifiability from Spherical Maps in a Closed
Spatial Geometry*, Theorem "Angular-channel rank bound".  The band `H_{≤L}` of scalar
eigenspaces on `S³` has dimension `N_L = Σ_{n≤L} (n+1)²`, and the paper's counting step is
`Σ_{ℓ=0}^{L} (2ℓ+1) min{q, L−ℓ+1} = N_L − N_{L−q}` (with `N_j = 0` for `j < 0`).

Machine-checked here (the representation-theoretic decomposition itself is not formalised;
only the exact count that turns it into the stated rank ceiling):
* `N_closed` : `6 N_L = (L+1)(L+2)(2L+3)`;
* `sector_count` : `Σ_{ℓ≤L} (2ℓ+1)(L−ℓ+1) = N_L` (dimension check of the decomposition);
* `rank_count` : `Σ_{ℓ≤L} (2ℓ+1) min{q, L−ℓ+1} + N_{L−q} = N_L` for all `q`, i.e. the
  ceiling equals `N_L − N_{L−q}`, and at least `N_{L−q}` directions are unidentifiable.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace FBS3R.Rank

open Finset

/-- `N_L = Σ_{n ≤ L} (n+1)²`. -/
def N (L : ℕ) : ℕ := ∑ n ∈ range (L + 1), (n + 1) ^ 2

/-- `N_j` on the integers, `0` for `j < 0`. -/
def Nz (j : ℤ) : ℕ := if j < 0 then 0 else N j.toNat

/-- The rank ceiling `Σ_{ℓ≤L} (2ℓ+1) min{q, L−ℓ+1}`. -/
def S (L q : ℕ) : ℕ := ∑ l ∈ range (L + 1), (2 * l + 1) * min q (L - l + 1)

theorem N_closed (L : ℕ) : 6 * N L = (L + 1) * (L + 2) * (2 * L + 3) := by
  induction L with
  | zero => simp [N]
  | succ k ih =>
    rw [N, sum_range_succ, ← N, mul_add, ih]; ring

lemma sum_odd (n : ℕ) : ∑ l ∈ range n, (2 * l + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; ring

lemma N_step (k : ℕ) : N k = Nz ((k : ℤ) - 1) + (k + 1) ^ 2 := by
  rcases k with _ | k
  · simp [N, Nz]
  · have h : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
    rw [h, Nz, if_neg (by omega), Int.toNat_natCast, N, sum_range_succ, ← N]

lemma min_succ (q m : ℕ) : min (q + 1) m = min q m + if q < m then 1 else 0 := by
  split_ifs <;> omega

theorem rank_count (L q : ℕ) : S L q + Nz ((L : ℤ) - q) = N L := by
  induction q with
  | zero => simp [S, Nz]
  | succ q ih =>
    have hS : S L (q + 1) = S L q +
        ∑ l ∈ range (L + 1), (2 * l + 1) * (if q < L - l + 1 then 1 else 0) := by
      simp only [S, min_succ, mul_add, sum_add_distrib]
    have hfilt : ∑ l ∈ range (L + 1), (2 * l + 1) * (if q < L - l + 1 then 1 else 0)
        = if q ≤ L then (L - q + 1) ^ 2 else 0 := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [← sum_filter]
      split_ifs with hq
      · have : (range (L + 1)).filter (fun l => q < L - l + 1) = range (L - q + 1) := by
          ext l; simp only [mem_filter, mem_range]; omega
        rw [this, sum_odd]
      · have : (range (L + 1)).filter (fun l => q < L - l + 1) = ∅ := by
          ext l; simp only [mem_filter, mem_range, Finset.notMem_empty, iff_false]; omega
        rw [this, sum_empty]
    rw [hS, hfilt]
    split_ifs with hq
    · have e : ((L : ℤ) - q) = ((L - q : ℕ) : ℤ) := by push_cast [hq]; ring
      have h1 := N_step (L - q)
      have e2 : ((L - q : ℕ) : ℤ) - 1 = (L : ℤ) - ↑(q + 1) := by push_cast [hq]; ring
      rw [e2] at h1
      rw [e, Nz, if_neg (by omega), Int.toNat_natCast] at ih
      omega
    · have h1 : Nz ((L : ℤ) - ↑(q + 1)) = 0 := by rw [Nz, if_pos (by push_cast; omega)]
      have h2 : Nz ((L : ℤ) - q) = 0 := by
        rcases Nat.lt_or_ge L q with h | h
        · rw [Nz, if_pos (by omega)]
        · omega
      rw [h1]; rw [h2] at ih; omega

/-- Dimension check `Σ_{ℓ≤L} (2ℓ+1)(L−ℓ+1) = N_L` (take `q = L + 1`). -/
theorem sector_count (L : ℕ) : ∑ l ∈ range (L + 1), (2 * l + 1) * (L - l + 1) = N L := by
  have h := rank_count L (L + 1)
  have hz : Nz ((L : ℤ) - ↑(L + 1)) = 0 := by rw [Nz, if_pos (by push_cast; omega)]
  rw [hz, add_zero, S] at h
  rw [← h]
  apply sum_congr rfl
  intro l hl
  rw [mem_range] at hl
  congr 1; omega

end FBS3R.Rank
