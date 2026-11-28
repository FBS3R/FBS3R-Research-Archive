/-
# Explicit eighth moment generating function (kernel-checked for all `n`)

The traces `M 8 n = Tr Aₙ⁸` for `n ≤ 10` are computed by the proved-correct bit-mask dynamic
programme of `APEX.PXP.MaskDP` (`M_eq_Mnat`), evaluated by the Lean kernel
(`decide +kernel`, no `native_decide`).  Since the numerator has degree `≤ 10`
(`pxp_moment_rational`), this yields, for **every** chain length,

`∑ₙ Tr Aₙ⁸ zⁿ = (2z + 22z² + 716z³ + 1146z⁴ + 8236z⁵ − 206z⁶ + 13114z⁷ − 8308z⁸ + 3152z⁹
  − 568z¹⁰) / (1 − z − z²)⁵`.
-/
import APEX.PXP.Explicit
import APEX.PXP.MaskDP

namespace APEX.PXP

open PowerSeries

set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma Mnat8_vals : (List.range 11).map (MaskDP.Mnat 8) =
    [0, 2, 32, 866, 5296, 30096, 115636, 401166, 1206848, 3371598, 8789188] := by
  decide +kernel

/-- `Tr Aₙ⁸` for `n = 0, …, 10`. -/
theorem M8_vals : M 8 0 = 0 ∧ M 8 1 = 2 ∧ M 8 2 = 32 ∧ M 8 3 = 866 ∧ M 8 4 = 5296 ∧
    M 8 5 = 30096 ∧ M 8 6 = 115636 ∧ M 8 7 = 401166 ∧ M 8 8 = 1206848 ∧ M 8 9 = 3371598 ∧
    M 8 10 = 8789188 := by
  have h := Mnat8_vals
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only [MaskDP.M_eq_Mnat, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  norm_num

theorem eighth_moment_gf :
    PowerSeries.mk (fun n => M 8 n) * (1 - X - X ^ 2) ^ 5 =
      ((2 * Polynomial.X + 22 * Polynomial.X ^ 2 + 716 * Polynomial.X ^ 3
        + 1146 * Polynomial.X ^ 4 + 8236 * Polynomial.X ^ 5 - 206 * Polynomial.X ^ 6
        + 13114 * Polynomial.X ^ 7 - 8308 * Polynomial.X ^ 8 + 3152 * Polynomial.X ^ 9
        - 568 * Polynomial.X ^ 10 : Polynomial ℤ) : PowerSeries ℤ) := by
  have e := numerator_eq 4 (by norm_num)
    (2 * Polynomial.X + 22 * Polynomial.X ^ 2 + 716 * Polynomial.X ^ 3
        + 1146 * Polynomial.X ^ 4 + 8236 * Polynomial.X ^ 5 - 206 * Polynomial.X ^ 6
        + 13114 * Polynomial.X ^ 7 - 8308 * Polynomial.X ^ 8 + 3152 * Polynomial.X ^ 9
        - 568 * Polynomial.X ^ 10)
  simp only [show 2 * 4 = 8 by rfl, show 4 + 1 = 5 by rfl] at e
  apply e
  · compute_degree!
  · intro n hn
    set S := PowerSeries.mk (fun n => M 8 n) with hS
    have hD : S * (1 - X - X ^ 2) ^ 5 =
        X ^ 0 * S - 5 * (X ^ 1 * S) + 5 * (X ^ 2 * S) + 10 * (X ^ 3 * S) - 15 * (X ^ 4 * S)
        - 11 * (X ^ 5 * S) + 15 * (X ^ 6 * S) + 10 * (X ^ 7 * S) - 5 * (X ^ 8 * S)
        - 5 * (X ^ 9 * S) - X ^ 10 * S := by ring
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := M8_vals
    rw [hD]
    simp only [map_sub, map_add, hS, coeff_X_pow_mul_mk]
    norm_num at hn
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, coeff_X_pow_mul_mk,
      Polynomial.coeff_X_pow, Polynomial.coeff_X]

end APEX.PXP
