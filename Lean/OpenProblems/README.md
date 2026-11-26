# OpenProblems — machine-checked results on catalogue problems (Lean 4 + Mathlib)

Lean 4.36.0, Mathlib v4.36.0. No `sorry`, no `native_decide`; every main theorem depends only on
`propext`, `Classical.choice`, `Quot.sound` (see `scripts/Axioms.lean`). Large finite checks use
`decide +kernel`, which is checked by the Lean kernel itself.

```
lake build OpenProblems
lake env lean scripts/Axioms.lean
```

**Honesty note.** None of the results below solves an open problem. All of the mathematics is
known (several items were settled in 2026 by other people). What is new is the machine-checked
proof: for items 1–12 the catalogue `google-deepmind/formal-conjectures` states the result with
proof `sorry` and no linked formal proof; items 13–18 are listed in Mathlib's `docs/1000.yaml`
without a formalization. We checked Mathlib and formal-conjectures only, not every other proof
assistant library.

| # | Module | Statement | Source | Kind |
|---|--------|-----------|--------|------|
| 1 | `Hyperperfect` | `two_hyperperfect_characterization` is **false**: Violette's 2-hyperperfect number `N = 3^16·q₁q₂q₃` is not of McCranie's form | formal-conjectures, Wikipedia/HyperperfectNumber | first formal proof (refutation) |
| 2 | `Erdos318` | `erdos_318.variants.contain_single_even` | formal-conjectures, Erdős 318 | first formal proof |
| 3 | `Erdos939` | `(Erdos939Sums 6).Infinite` (case `r = 6` of `infinite_of_six_le`) | Erdős 939 | first formal proof, special case |
| 4 | `Erdos939` | `erdos_939.variants.finite` | Erdős 939 | first formal proof |
| 5 | `Erdos939` | `erdos_939.variants.seven` | Erdős 939 | first formal proof |
| 6 | `Erdos939` | `erdos_939.variants.eight` | Erdős 939 | first formal proof |
| 7 | `Ramsey` | `R(3,3) = 6` | formal-conjectures, Wikipedia/RamseyNumbers | first proof of the catalogue statement |
| 8 | `Ramsey` | `R(3,4) = 9` | same | same |
| 9 | `Ramsey` | `R(3,5) = 14` | same | same |
| 10 | `Ramsey` | `R(4,4) = 18` | same | same |
| 11 | `WOWII91` | Written on the Wall II, Conjecture 91 is **false** (11-vertex counterexample, `α : Type`) | formal-conjectures, WrittenOnTheWallII | first formal proof (refutation) |
| 12 | `TriangleRamsey` | `R(3,3,3) = 17` (Greenwood–Gleason) with the definitions of Erdős 183 | formal-conjectures definitions | new formal statement + proof |
| 13 | `Thabit` | Thābit ibn Qurra's amicable-pair theorem | Mathlib 1000 | first Mathlib-based formalization |
| 14 | `Proth` | Proth's primality theorem | Mathlib 1000 | same |
| 15 | `Lame` | Lamé's theorem on the Euclidean algorithm | Mathlib 1000 | same |
| 16 | `MirskyNewman` | Mirsky–Newman: no exact covering system with distinct moduli | Mathlib 1000 | same |
| 17 | `Bondy` | Bondy's theorem on distinguishing sets | Mathlib 1000 | same |
| 18 | `Midy` | Midy's theorem on repeating decimals | Mathlib 1000 | same |

Reusable infrastructure: `Lucas.lean` (Lucas–Pratt certificates with a kernel-evaluable
`powMod`, proving primality of 30-digit numbers in a few seconds), Boolean clique checkers
(`Ramsey.free3/4/5`, `WOWII91.free2/3/4`) with soundness proofs, used instead of
`Finset.powersetCard` enumerations, which exhaust the kernel's memory.

Caveats recorded in the files:
* Ramsey values are proved as `sInf {n | IsGraphRamsey n k l} = R`; the catalogue's
  `classicalRamsey_eq_sInf` identifies this with its `R(k, l)`.
* WOWII 91 is refuted for `α : Type` (universe 0); the catalogue quantifies over `Type*`.
* Item 3 covers only `r = 6`; `r ≥ 7` remains a `sorry` in the catalogue.

The full write-up is `report/OpenProblems_Report.tex`.
