# FBS3R-W034: corrected scientific edition (errata only)

- **Title:** Compact Simply-Connected Cosmology and the Geometric Origin of Quantum Nonlocality: Bell Inequality Violations from S³ Topology and Fibonacci Geodesic Stratification
- **Original path (unchanged):** `/home/claude/repo/All Preprints/2026_04_15_Compact_Simply_Connected_Cosmology_and_the_Geometric_Origin_of_Quantum_Nonlocality_Bell_Inequality_Violations_from_S3_Topology_and_Fibonacci_Geodesic_Stratification/2026_04_15_Compact_Simply_Connected_Cosmology_and_the_Geometric_Origin_of_Quantum_Nonlocality_Bell_Inequality_Violations_from_S3_Topology_and_Fibonacci_Geodesic_Stratification.pdf`
- **Audit status of the work:** DISPROVED (pass 2)
- **Prepared:** 2026-11-28 by the APEX auditor. This is not a rewrite of the paper: it lists errata and their consequences only.

## Errata

### E1. FBS3R-W034#0 (A2)

**Original text (quoted from the paper):**

> Theorem 4.5 (Uniqueness of the Fibonacci Stratification). Among all non-overlapping … convergent ratio a_{n+1}/a_n → r > 1, the Fibonacci partition (with r = φ) is the unique minimally redundant gapless self-similar indexing.

**Refutation:** The hypotheses are inconsistent. No strictly increasing a : ℕ → ℕ with a 0 = 1 that is closed under addition has a_{n+1}/a_n → r > 1 (FBS3R.FibStrat.no_additively_closed_partition_with_ratio_gt_one). The Fibonacci numbers themselves are not additively closed: F₂ + F₅ = 6 (FBS3R.FibStrat.fib_not_additively_closed).

**Corrected statement (true):** (i) The Fibonacci intervals [F_n, F_{n+1}), n ≥ 2, partition ℤ≥1: every m ≥ 1 lies in exactly one (FBS3R.FibStrat.fib_partition, B30). (ii) The class of additively closed, strictly increasing ℕ-sequences starting at 1 with ratio limit r > 1 is empty, so the uniqueness theorem is vacuous. No uniqueness statement for the Fibonacci partition is proved.

**Justification / Lean:** refuting declarations: `FBS3R.FibStrat.no_additively_closed_partition_with_ratio_gt_one`, `FBS3R.FibStrat.fib_not_additively_closed`. Corrected statement: KERNEL_PROVED in FBS3R-Lean (B30 + A2); no APEX id.

**Dependent claims:**

- FBS3R-W034#3: HEURISTIC/PHYSICAL_MODEL → **UNSUPPORTED_AFTER_REFUTATION**. Thm 4.8 (Bell nonlocality from hyperconnectivity) uses Def. 4.7, F_k = F_m + F_n for every pair, which is exactly the false additive closure (fib_not_additively_closed), and §4.6 invokes Thm 4.5.
- FBS3R-W034#5: KERNEL_PROVED → **unchanged**. The partition (B30) is the true residue of A2.

**Checked, not dependent:** W030 (Noether identities) and W040 (quasi-local charges) appeal to the Zeckendorf–Lekkerkerker uniqueness theorem, which is true. They do not use Thm 4.5. W046 Prop. II.4 uses only the band partition (B30). W042 lists W034 only as bibliography item [9] and never cites it in the text.

### E2. FBS3R-W034#1 (A3)

**Original text (quoted from the paper):**

> Consider a maximally entangled two-qubit state |Φ+⟩ = (|00⟩ + |11⟩)/√2. … E(a, b) = ⟨Φ+|(σ·a) ⊗ (σ·b)|Φ+⟩ = −cos θ_ab (Theorem 3.3).

**Refutation:** For Φ⁺: ⟨σx⊗σx⟩ = +1, ⟨σy⊗σy⟩ = −1, ⟨σz⊗σz⟩ = +1 (FBS3R.Bell.bell_Phi_plus, stated for the unnormalised vector with values 2, −2, 2). So E(a,a) = +1 for a = x, not −1.

**Corrected statement (true):** For the singlet |Ψ⁻⟩ = (|01⟩ − |10⟩)/√2: E(a,b) = −a·b = −cos θ_ab (axis values −1, −1, −1: FBS3R.Bell.singlet_Psi_minus; full kernel, CHSH −2√2 and Chern rigidity q = ±1 in W043: B26–B28). For Φ⁺: E(a,b) = a_x b_x − a_y b_y + a_z b_z.

**Justification / Lean:** refuting declarations: `FBS3R.Bell.bell_Phi_plus`, `FBS3R.Bell.singlet_Psi_minus`. Corrected statement: KERNEL_PROVED in FBS3R-Lean (B25–B28, A3 singlet part); the general Φ⁺ bilinear form is classical and not formalized beyond the axis values.

**Dependent claims:**

- FBS3R-W034#7: HEURISTIC/PHYSICAL_MODEL → **UNSUPPORTED_AFTER_REFUTATION**. Cor. 5.3 (Tsirelson excess ∝ c₁) is derived from Thm 3.3 with the Φ⁺ kernel (Conclusions item 2–3).
- FBS3R-W034#3: HEURISTIC/PHYSICAL_MODEL → **UNSUPPORTED_AFTER_REFUTATION**. Also uses §5.1 (Φ⁺).
- FBS3R-W034#4: KNOWN_RESULT → **unchanged**. Tsirelson is state-independent.

**Checked, not dependent:** W043 (PRA version) uses the singlet and is the corrected edition (KERNEL_PROVED B25–B29). W058 cites only W043.

## Impact on the work's conclusions

The headline conclusion ('Bell violations are a geometric theorem about S³, filled by the unique Fibonacci stratification') loses both pillars. Uniqueness (Thm 4.5) is vacuous (A2). Hyperconnectivity (Def. 4.7 / Thm 4.8) requires F_k = F_m + F_n, which is false. The Berry-phase kernel (Thm 3.3 / §5.1) is wrong for Φ⁺ (A3). What survives: CHSH ≤ 2 for LHV (B25), the singlet Tsirelson kernel (B26), the Fibonacci partition (B30), and the corrected singlet computation as presented in the PRA version W043. Cor. 5.3 and the 'geometric origin' interpretation become UNSUPPORTED_AFTER_REFUTATION.
