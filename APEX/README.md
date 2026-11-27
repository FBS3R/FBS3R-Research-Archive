# FBS3R–APEX — исследовательская ветка `research/fbs3r-apex`

Начата 27 ноября 2026 г. Ветка не сливается в `main` автоматически; оригинальные работы архива не изменены.
Основа: `Lean/FBS3R-Lean` (ветка `claude/project-thread-3m61og`, 04115e1) и `Lean/OpenProblems`
(ветка `claude/project-thread-q9utq4`, b2c7f28) — обе влиты сюда без изменений.

## Раунды 1–4: что принято

Полный список раунда 4 — `Audit/APEX_RESULTS.json` (20 результатов, 137 целей в `Audit/ACCEPTED_THEOREMS.txt`).
 (проверено ядром Lean, только `propext`, `Classical.choice`, `Quot.sound`)

| ID | Утверждение | Lean |
|---|---|---|
| APEX-PXP-1 | `(Σₙ Tr Aₙ^{2m} zⁿ)(1−z−z²)^{m+1} = P_m(z)`, `P_m ∈ ℤ[z]`, `deg P_m ≤ 3m−2`, для всех `m ≥ 1` (в препринте 2026-10-23: `≤ 3m+2`) | `APEX.PXP.pxp_moment_rational` |
| APEX-PXP-2 | `P_m ≡ (2m)!·z^{2m−1} (mod 1−z−z²)`; `1−z−z²` не делит `P_m`, т.е. знаменатель точен | `APEX.PXP.pxp_moment_residue`, `pxp_denominator_sharp` |
| APEX-PXP-3 | `deg P_m = 3m−2` ровно; старший коэффициент имеет знак `(−1)^{m−1}` | `APEX.PXP.pxp_numerator_natDegree` |
| APEX-COL-1 | Ускоренное отображение Коллатца `T`: `T^j(2^{L+1}−1) = 3^j·2^{L+1−j}−1` (j ≤ L); не существует ограниченной `b` с `log T(n) + b(T n) ≤ log n + b(n)` для всех нечётных `n`; `φ² < 3 < φ³` | `APEX.Collatz.no_bounded_log_correction` |
| APEX-BLK-1 | Блокада радиуса r: `aₙ = n+1` (n ≤ r), `aₙ = aₙ₋₁ + aₙ₋ᵣ₋₁`, т.е. `Σ aₙ zⁿ = (1+…+z^r)/(1−z−z^{r+1})`; при r = 1 это `F_{n+2}` | `APEX.Blockade.a_rec`, `gf_coeff` |
| APEX-PXP-5 | явные формулы 4-го и 6-го моментов препринта, для всех n | `APEX.PXP.fourth_moment_gf`, `sixth_moment_gf` |

`Aₙ` — матрица смежности Фибоначчиева куба Γₙ (открытая PXP-цепочка, единичные связи, без поля), определена в
`APEX/Lean/APEX/PXP/Walks.lean` как 0/1-матрица отношения «обе конфигурации допустимы и отличаются ровно в одном узле».

## Структура

* `Lean/` — Lean-пакет (Lean 4.36.0, Mathlib v4.36.0): `APEX/PXP/{Trajectories,Rational,Walks,Main,Explicit,Residue,Degree}.lean`, `scripts/Axioms.lean`.
* `Certificates/pxp_verify.py` — независимая проверка точной целочисленной арифметикой (только stdlib).
* `Manuscripts/2026_11_27_Sharp_Rational_Hierarchy_PXP_Moments_Lean4.tex` — статья (не скомпилирована: в контейнере нет LaTeX).
* `Audit/` — `CLAIMS.jsonl`, `THEOREM_DEPENDENCIES.json`, `OPEN_PROBLEMS.json`, `COUNTEREXAMPLES.md`, `NOVELTY_AUDIT.md`,
  `COVERAGE_MATRIX.csv`, `PROOF_MANIFEST.json`, `AXIOM_REPORT.txt`, `BUILD_LOG.txt`, `SHA256SUMS.txt`, `RED_TEAM.md`,
  `RESEARCH_FRONTIER.md`, `NEXT_MISSIONS.md`.

Каталоги `Foundations/`, `Geometry/`, `QuantumGravity/`, `Cosmology/`, `YangMills/`, `NavierStokes/`, `NumberTheory/`,
`QuantumInformation/`, `Topology/`, `OpenProblems/`, `Counterexamples/`, `Literature/` из плана миссии появятся, когда в них будет
принятый результат; пустые каталоги не создаются.

## Чего здесь нет

Ни одна из проблем тысячелетия, гипотеза Коллатца, MLC и другие крупные открытые задачи в этом раунде не решены и не продвинуты.

## Воспроизведение

```
cd APEX/Lean && lake build && lake env lean scripts/Axioms.lean
python3 -I APEX/Certificates/pxp_verify.py 15 4
python3 -I APEX/Certificates/blockade_verify.py 22 3
bash APEX/ci_check.sh
```
Без кэша Mathlib первая сборка компилирует Mathlib из исходников (≈45 минут на 4 ядрах).
