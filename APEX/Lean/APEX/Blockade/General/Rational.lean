import APEX.Blockade.General.Arrays

/-!
# Range-`r` blockade, all even moments: rationality and the numerator degree bound

**Theorem (`moment_rational`).**  For every `r ≥ 1` and `m ≥ 1` there is `P ∈ ℤ[z]` with
`deg P ≤ (2r+1)(m−1)+1` and
`(∑ₙ Tr (A_{n,r})^{2m} zⁿ) · (1 − z − z^{r+1})^{m+1} = P` (formal power series over `ℤ`),
where `A_{n,r} = adjMat r n` is the adjacency matrix of the range-`r` constrained hypercube.

For `r = 1` this is `APEX.PXP.pxp_moment_rational` (degree `3m − 2`).
-/

namespace APEX.Blockade.General

open Finset PowerSeries

theorem series_Mk_eq_Φ {r : ℕ} (hr : 1 ≤ r) (k : ℕ) [NeZero k] :
    PowerSeries.mk (fun n => Mk k r n) = Φ r (univ : Finset (Fin k)) := by
  ext n
  rw [coeff_mk, Mk, trace_eq_N hr n, Φ, Gs, coeff_mk]

/-- **Milestone (a)**: universal denominator `D_r^{m+1}` and numerator degree
`≤ (2r+1)(m−1)+1`, for all `m ≥ 1`, `r ≥ 1`. -/
theorem moment_rational {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    ∃ P : Polynomial ℤ, P.natDegree ≤ (2 * r + 1) * (m - 1) + 1 ∧
      PowerSeries.mk (fun n => Mk (2 * m) r n) * (1 - X - X ^ (r + 1)) ^ (m + 1) =
        (P : PowerSeries ℤ) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨P, hP, hS⟩ := good_free_univ hr hm
  refine ⟨P, hP, ?_⟩
  rw [series_Mk_eq_Φ hr]
  exact hS

end APEX.Blockade.General

