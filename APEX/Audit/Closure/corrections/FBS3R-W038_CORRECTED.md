# FBS3R-W038: corrected scientific edition (errata only)

- **Title:** Hierarchical Bethe-Type States on Fibonacci Graphs over S³
- **Original path (unchanged):** `/home/claude/repo/All Preprints/2026_04_21_Hierarchical_Bethe_Type_States_on_Fibonacci_Graphs_over_S3/2026_04_21_Hierarchical_Bethe_Type_States_on_Fibonacci_Graphs_over_S3.pdf`
- **Audit status of the work:** DISPROVED (pass 2)
- **Prepared:** 2026-11-28 by the APEX auditor. This is not a rewrite of the paper: it lists errata and their consequences only.

## Errata

### E1. FBS3R-W038#0 (A6)

**Original text (quoted from the paper):**

> Theorem 1 (Fibonacci scaling). The shifted sequence (1) [F1 = 3, F2 = 5, F_{n+1} = F_n + F_{n−1}] satisfies F_n = (φ^{n+2} − ψ^{n+2})/√5, so that F_n = φ^{n+2}/√5 + O(φ^{−n}).

**Refutation:** At n = 1 the formula gives (φ³ − ψ³)/√5 = 2 ≠ 3 = F₁ (FBS3R.Checks.paper_binet_wrong).

**Corrected statement (true):** F_n = Fib(n+3) = (φ^{n+3} − ψ^{n+3})/√5 for all n (FBS3R.Checks.F_binet), hence F_n = φ^{n+3}/√5 + O(φ^{−n}). The ratio limit F_{n−1}/F_n → φ^{−1} (eq. 9) remains true.

**Justification / Lean:** refuting declarations: `FBS3R.Checks.paper_binet_wrong`, `FBS3R.Checks.F_binet`. Corrected statement: KERNEL_PROVED in FBS3R-Lean (F_binet); no APEX id.

**Dependent claims:**

- FBS3R-W038 eq. (8) asymptotic (not a separate audit claim): (part of #0) → **CORRECTED: φ^{n+3}/√5**. Direct consequence.
- FBS3R-W038#1: KERNEL_PROVED → **unchanged**. Zero-mode bound uses F_{n−1} as a cardinality, not Binet.
- FBS3R-W038#2: OPEN → **OPEN (unaffected)**. Schur recursion uses only block sizes.

**Checked, not dependent:** 'Bethe' and the shifted sequence F1 = 3 occur only in W038.

## Impact on the work's conclusions

Only the exponent changes: F_n = Fib(n+3), with asymptotic φ^{n+3}/√5. The ratio limit φ^{-1}, the zero-mode bound (B36) and the Schur-complement recursions are unaffected. Any downstream numeric use of φ^{n+2}/√5 (e.g. state counts) is low by a factor φ.
