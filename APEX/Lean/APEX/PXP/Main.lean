/-
# Universal rational hierarchy for PXP spectral moments — main theorem

For the open PXP chain with unit couplings and no field, `Aₙ` = adjacency matrix of the
Fibonacci cube `Γₙ`, put `M_{m,n} = Tr Aₙ^{2m}`.

**Theorem (`pxp_moment_rational`).**  For every `m ≥ 1` there is `P_m ∈ ℤ[z]` with
`deg P_m ≤ 3m - 2` and
`(∑ₙ M_{m,n} zⁿ) · (1 - z - z²)^(m+1) = P_m(z)`  (identity of formal power series over `ℤ`).

This strengthens the bound `deg P_m ≤ 3m + 2` stated in *Rational Spectral Hierarchies and
Matrix-Free Gauge Certificates* (2026-10-23, Theorem `th:denom`).  The proof is independent of
the paper's resolvent argument: it is a strong induction over the set of used time labels,
with the degree bookkeeping predicate `Good`.
-/
import APEX.PXP.Walks

namespace APEX.PXP

open Finset PowerSeries

/-- `M k n = Tr (Aₙ)^k`. -/
noncomputable def M (k n : ℕ) : ℤ := Matrix.trace (adjMat n ^ k)

theorem M_eq_sum_g (k : ℕ) [NeZero k] (n : ℕ) :
    M k n = ∑ β : Traj k, (g n β univ : ℤ) := by
  unfold M adjMat
  rw [trace_relMat_pow, card_walks_eq_card_arrays]
  cases n with
  | zero =>
    simp only [g, Nat.cast_zero, Finset.sum_const_zero]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [if_neg]
    rintro ⟨-, -, h⟩
    have : (0 : Fin k) ∈ U a := by rw [h]; exact mem_univ _
    simp [U] at this
  | succ n =>
    simp_rw [g_succ_eq_count]
    unfold count
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_eq_single (a (Fin.last n))]
    · simp
    · intro β _ hβ
      rw [if_neg]
      rintro ⟨-, -, -, h⟩
      exact hβ h.symm
    · simp

theorem series_M_eq_T (k : ℕ) [NeZero k] :
    PowerSeries.mk (fun n => M k n) = T (univ : Finset (Fin k)) := by
  ext n
  rw [coeff_mk, M_eq_sum_g, T, map_sum]
  simp [G]

/-- **Universal denominator and sharp numerator-degree bound** (all even moment orders). -/
theorem pxp_moment_rational (m : ℕ) (hm : 1 ≤ m) :
    ∃ P : Polynomial ℤ, P.natDegree ≤ 3 * m - 2 ∧
      PowerSeries.mk (fun n => M (2 * m) n) * (1 - X - X ^ 2) ^ (m + 1) = (P : PowerSeries ℤ) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨P, hP, hPT⟩ := good_total (k := 2 * m) (by omega)
  refine ⟨P, ?_, ?_⟩
  · simpa using hP
  · rw [series_M_eq_T]
    have : 2 * m / 2 = m := by omega
    rw [this] at hPT
    exact hPT

end APEX.PXP
