# FBS3R-W024: corrected scientific edition (errata only)

- **Title:** Zeckendorf–φ Bounds for the Collatz Map
- **Original path (unchanged):** `/home/claude/repo/All Preprints/2025_09_28_Zeckendorf_φ_Bounds_for_the_Collatz_Map_Strict_Local_Theory_Two_Sufficient_Reductions_and_No_Go_Results/2025_09_28_Zeckendorf_φ_Bounds_for_the_Collatz_Map_Strict_Local_Theory_Two_Sufficient_Reductions_and_No_Go_Results.pdf`
- **Audit status of the work:** DISPROVED (pass 2)
- **Prepared:** 2026-11-28 by the APEX auditor. This is not a rewrite of the paper: it lists errata and their consequences only.

## Errata

### E1. FBS3R-W024#2 (A1)

**Original text (quoted from the paper):**

> Proposition 2 (Refined odd-step). If n is top-third then h(3n+1) − h(n) ≤ 3; otherwise the increase is ≤ 2.

**Refutation:** n = 11: x = log_φ(√5·11) ∈ [6, 6+2/3), so 11 is not top-third, yet h(34) = h(11) + 3. Lean: FBS3R.Collatz.refined_odd_step_counterexample.

**Corrected statement (true):** For every n ≥ 1: h(n) + 2 ≤ h(3n+1) ≤ h(n) + 3 (APEX.Collatz.fibHeight_three_mul_add_one). In each Fibonacci layer [F_k, F_{k+1}) (k ≥ 2), exactly ⌊(F_{k+1} − F_k + 1)/3⌋ integers have gain 3 (APEX.Collatz.card_gain_three). Gain 3 is not confined to top-third n. The superstep drift is h(T n) − h(n) ≤ 3 − ν₂(3n+1) (B3).

**Justification / Lean:** refuting declarations: `FBS3R.Collatz.refined_odd_step_counterexample`. Corrected statement: KERNEL_PROVED (APEX-COL-2; FBS3R B2, B3). APEX: APEX-COL-2.

**Dependent claims:**

- FBS3R-W024#4: OPEN → **UNSUPPORTED_AFTER_REFUTATION (B' part)**. Inequality (2) k_{J+1} − k_J ≤ (2 + I_J) − A_J, Thm 1 (conditional descent) and Thm 5 (B', integrand 2 + I − ν₂) use Prop. 2. The corrected versions use 3 − ν₂ (the paper's Remark 2). Reduction A' (Thm 4) does not use Prop. 2, but its conclusion is unsatisfiable for all odd n > 1 by APEX-COL-1 no_bounded_height_correction.
- FBS3R-W024 Thm 1 (conditional descent; not a separate audit claim): (part of #4) → **UNSUPPORTED_AFTER_REFUTATION; corrected: hypothesis liminf A_J ≥ 3 + ε**. Uses (2).
- FBS3R-W024 Thm 3 (no uniform negativity): (not listed) → **unaffected**. δ₁ witness works with either integrand.

**Checked, not dependent:** 'Collatz' and 'top-third' occur only in W024; no other work depends on it.

## Impact on the work's conclusions

The correct local bounds (B1–B3, APEX-COL-2) are unaffected. Inequality (2), Theorem 1 (conditional descent) and Theorem 5 (Reduction B') must be restated with the integrand 3 − ν₂ in place of 2 + I − ν₂, which strengthens their hypotheses. Reduction A' does not use Prop. 2, but by APEX-COL-1 its certificate cannot exist when it is required for all odd n > 1. The paper's statement that 'either reduction implies Collatz' therefore holds only in the weak sense that B' is a sufficient (and essentially Collatz-equivalent) hypothesis. The paper never claimed convergence, and Collatz remains open.
