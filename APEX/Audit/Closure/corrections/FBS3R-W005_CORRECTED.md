# FBS3R-W005: corrected scientific edition (errata only)

- **Title:** Rigorous Mathematical Proof of the Local Connectivity of the Mandelbrot Set
- **Original path (unchanged):** `/home/claude/repo/All Preprints/2025_03_05_Rigorous Mathematical Proof of the Local Connectivity of the Mandelbrot Set/2025_03_05_Rigorous Mathematical Proof of the Local Connectivity of the Mandelbrot Set.pdf`
- **Audit status of the work:** DISPROVED (pass 2)
- **Prepared:** 2026-11-28 by the APEX auditor. This is not a rewrite of the paper: it lists errata and their consequences only.

## Errata

### E1. FBS3R-W005#1 (A5)

**Original text (quoted from the paper):**

> Therefore, the intersection U – as a subset of this region – is also connected and contains c0.

**Refutation:** A subset of a connected set need not be connected. Kernel-checked counterexample {0,1} ⊆ [0,1]: FBS3R.Misc.subset_of_connected_not_connected : ∃ S T : Set ℝ, IsConnected T ∧ S ⊆ T ∧ S.Nonempty ∧ ¬ IsPreconnected S.

**Corrected statement (true):** U = {V < x_N} ∩ B(c0,ε) is an open subset of ℂ containing c0. Its connected component containing c0 is a connected open neighbourhood of c0 in ℂ, because open subsets of ℂ are locally connected. This says nothing about connectedness of M ∩ U, which is what local connectivity of the Mandelbrot set M requires. No correct version of the step yields MLC.

**Justification / Lean:** refuting declarations: `FBS3R.Misc.subset_of_connected_not_connected`. Corrected statement: standard topology (Mathlib: isOpen_connectedComponentIn / locallyConnectedSpace); no APEX id.

**Dependent claims:**

- FBS3R-W005#0: OPEN → **OPEN (problem); paper's proof UNSUPPORTED_AFTER_REFUTATION**. MLC conclusion of the paper rests on this step.
- FBS3R-W005#2: OPEN → **DISPROVED_PENDING_LEAN (independently false; see CLOSURE_PLAN W005#2)**. Second route (pi_1 = 0 => local connectivity) is itself false (harmonic fan / comb).

**Checked, not dependent:** Other works mentioning 'Mandelbrot' (W007, W014, W017, W020, W049, W070, W088) only cite Mandelbrot's 1982 book, use it as an image or list MLC as open; none relies on W005.

## Impact on the work's conclusions

The paper does not prove MLC. Its key step (A5) is false, and the alternative route (π₁ = 0 ⇒ local connectivity, claim #2) is false as an implication. MLC remains an open problem. No conclusion of the paper survives except restatements of known facts (connectedness of M, Douady–Hubbard).
