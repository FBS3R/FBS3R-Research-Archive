# FBS3R-W049: corrected scientific edition (errata only)

- **Title:** Benchmark Residual Invariants in Compact S³ Cosmology
- **Original path (unchanged):** `/home/claude/repo/All Preprints/2026_05_11_Benchmark_residual_invariants_in_compact_S3_cosmology/2026_05_11_Benchmark_residual_invariants_in_compact_S3_cosmology.pdf`
- **Erratum location:** `/home/claude/repo/All Preprints/2026_05_11_Benchmark_residual_invariants_in_compact_S3_cosmology/2026_05_11_Benchmark_residual_invariants_in_compact_S3_cosmology_supplement.tex` (Corollary `cor:spectra`, lines ~403–418). This file is unchanged too.
- **Audit status of the work:** DISPROVED (pass 2)
- **Prepared:** 2026-11-28 by the APEX auditor. This is not a rewrite of the paper: it lists errata and their consequences only.

## Errata

### E1. FBS3R-W049#3 (A7)

**Original text (quoted from the paper):**

> The exponential family A_n = A_0 e^{−βn}, β > 0, is admissible, with σ² = (A_0/2π²A³)·e^β(e^β+1)/(e^β−1)³.

**Refutation:** Σ_{n≥0}(n+1)² e^{−βn} = e^{2β}(e^β+1)/(e^β−1)³. The stated value is smaller by exactly the factor e^β (FBS3R.CosmoBench.paper_exp_variance_wrong); it is the value for A_n = A_0 e^{−β(n+1)}.

**Corrected statement (true):** For A_n = A_0 e^{−βn} (β > 0): σ² = (A_0/2π²A³)·e^{2β}(e^β+1)/(e^β−1)³. Equivalently, the paper's expression holds for A_n = A_0 e^{−β(n+1)}. The series identity is kernel-proved (exp_family_sum). The prefactor 1/(2π²A³) is taken from the paper's eq. (variance) and is not formalized.

**Justification / Lean:** refuting declarations: `FBS3R.CosmoBench.exp_family_sum`, `FBS3R.CosmoBench.paper_exp_variance_wrong`. Corrected statement: KERNEL_PROVED in FBS3R-Lean (exp_family_sum).

**Dependent claims:**

- FBS3R-W049#2: KERNEL_PROVED → **unchanged**. Power-law part of the same corollary is correct.
- FBS3R-W049#4: HEURISTIC/PHYSICAL_MODEL → **unchanged (check any numeric use of σ² for the exponential family)**. Manifest does not reference cor:spectra.

**Checked, not dependent:** cor:spectra is referenced nowhere else in the supplement or the main .tex. 'Benchmark' in W055, W081, W082, W095, W096 refers to unrelated benchmarks.

## Impact on the work's conclusions

Affects only the supplement's Cor. 'Benchmark spectra'. For A_n = A_0e^{−βn} the point variance is larger by e^β than stated, and admissibility (finiteness) is unchanged. The power-law criterion α > 3 (B62) and the background results (B60–B61) are unaffected. The main PDF does not contain the corollary.
