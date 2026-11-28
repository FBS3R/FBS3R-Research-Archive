# FBS3R-W036: corrected scientific edition (errata only)

- **Title:** Geometric Infrared Scale of Yang–Mills Theory on a Compact Three-Manifold: Discreteness, Spectral Threshold and Fibonacci Hierarchy
- **Original path (unchanged):** `/home/claude/repo/All Preprints/2026_04_19_Geometric_Infrared_Scale_of_Yang_Mills_Theory_on_a_Compact_Three_Manifold_Discreteness_Spectral_Threshold_and_Fibonacci_Hierarchy/2026_04_19_Geometric_Infrared_Scale_of_Yang_Mills_Theory_on_a_Compact_Three_Manifold_Discreteness_Spectral_Threshold_and_Fibonacci_Hierarchy.pdf`
- **Audit status of the work:** DISPROVED (pass 2)
- **Prepared:** 2026-11-28 by the APEX auditor. This is not a rewrite of the paper: it lists errata and their consequences only.

## Errata

### E1. FBS3R-W036#0 (A4)

**Original text (quoted from the paper):**

> Corollary II.2 (Threshold on S³). On S³(R) the lowest transverse vector Laplacian eigenvalue is λ^V_1 = 3/R², giving Δ(S³(R)) = √3/R. … yielding λ^V_ℓ = ℓ(ℓ+2)/R² for ℓ ≥ 1.

**Refutation:** ℓ(ℓ+2)/R² is the SCALAR Laplace spectrum on S³(R). For divergence-free (transverse) vector fields the archive's own spectra are curl² = (k+2)²/R² and Stokes k(k+4)/R² (k ≥ 0). 3 occurs in neither, and min curl² = 4/R² (FBS3R.KillingBeltrami.no_three_in_curl_or_stokes_spectrum: (k+2)² ≠ 3 ∧ k(k+4) ≠ 3 ∧ 4 ≤ (k+2)²).

**Corrected statement (true):** (i) In the spectra {(k+2)²/R²} (curl² = Hodge Laplacian on coexact 1-forms) and {k(k+4)/R²} (Stokes), 3/R² does not occur. The minimum of the first is 4/R², at k = 0 (Lean, A4). So the free linearised transverse-gluon threshold is Δ = 2/R, not √3/R (classical: Hodge spectrum of coexact 1-forms on S³ is (ℓ+1)²/R², ℓ ≥ 1; completeness is not formalized). (ii) 3/R² is the first nonzero eigenvalue of the SCALAR Laplacian. APEX-S3-2 proves that degree-n harmonic polynomials restrict to eigenfunctions with eigenvalue n(n+2)/R² (sphLapF_of_harmonic), so n = 1 gives 3/R². Completeness of that spectrum is not formalized. (iii) Any such threshold → 0 as R → ∞ (APEX-S3-2 tendsto_sphEigen), so it bounds no infinite-volume gap (APEX-YM-1 nonuniform_gap_lost).

**Justification / Lean:** refuting declarations: `FBS3R.KillingBeltrami.no_three_in_curl_or_stokes_spectrum`. Corrected statement: vector part KERNEL_PROVED as stated in (i) (FBS3R A4); scalar eigenfunction part APEX-S3-2; spectral completeness not formalized. APEX: APEX-S3-2 (scalar part); APEX-YM-1 (limit no-go).

**Dependent claims:**

- FBS3R-W036#3: HEURISTIC/PHYSICAL_MODEL → **UNSUPPORTED_AFTER_REFUTATION**. Δ = √3 Λ_QCD ≈ 520 MeV and the glueball hierarchy use λ₁ = 3/R² (A4) and the Fibonacci uniqueness (A2). With the corrected threshold the same convention gives Δ = 2Λ_QCD, which is still heuristic.
- FBS3R-W036#5: OPEN → **UNSUPPORTED_AFTER_REFUTATION**. The 'lower bound' claim is built on the refuted 3/R² and contradicts APEX-YM-1/S3-2.
- FBS3R-W036#4: OPEN → **OPEN (unchanged; Clay problem)**. The conjecture does not depend on the value of the threshold.

**Checked, not dependent:** W066 Prop. 15.x and W068 Prop. 16.4 use a 'gap template' √3/R taken from the SCALAR spectrum ℓ(ℓ+2)/R², which is consistent with APEX-S3-2. Both state explicitly that it is not a YM mass gap (W066 #3 and W068 #3 are KERNEL_PROVED no-go). Not dependent on A4, but the label 'gap template' should not be read as a gluon threshold. W056 uses the scalar spectrum l(l+2)/R² correctly.

### E2. FBS3R-W036#1 (A2)

**Original text (quoted from the paper):**

> Theorem IV.5 (Natural minimal-redundancy partition). … minimal redundancy, the Fibonacci partition is the unique … spectral coarse-graining of the S³ …

**Refutation:** Same as A2 (FBS3R.FibStrat.no_additively_closed_partition_with_ratio_gt_one): the hypothesis class is empty.

**Corrected statement (true):** The Fibonacci intervals partition ℤ≥1 (B30, fib_partition = W036#2, KERNEL_PROVED). Uniqueness is vacuous.

**Justification / Lean:** refuting declarations: `FBS3R.FibStrat.no_additively_closed_partition_with_ratio_gt_one`. Corrected statement: KERNEL_PROVED in FBS3R-Lean (B30).

**Dependent claims:**

- FBS3R-W036#3: HEURISTIC/PHYSICAL_MODEL → **UNSUPPORTED_AFTER_REFUTATION**. Glueball hierarchy m_{n+1}/m_n → φ is motivated by the 'natural' Fibonacci bands.
- FBS3R-W036#2: KERNEL_PROVED → **unchanged**. Partition itself is true.

## Impact on the work's conclusions

Result (2) of the paper (λ₁^V = 3/R², Δ = √3/R, Δ ≈ 520 MeV) is wrong. The transverse threshold of the archive's own curl² spectrum is 4/R² (Δ = 2/R), and 3/R² is the scalar eigenvalue. Result (3) (natural/unique Fibonacci partition) reduces to the true partition statement B30, with uniqueness vacuous (A2). Result (4) (glueball hierarchy, m₃/m₁) inherits both errors and becomes UNSUPPORTED_AFTER_REFUTATION. Any finite-volume threshold → 0 as R → ∞, so the abstract's 'lower bound for the infinite-volume gap' is unsupported (APEX-YM-1, APEX-S3-2). The YM mass gap (Conjecture V.1) stays OPEN.
