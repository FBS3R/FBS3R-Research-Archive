# Аудит новизны (раунды 1–2)

Правило: «NEW_THEOREM_CANDIDATE» означает только, что поиск не нашёл утверждения в литературе. Это не заявка на мировой приоритет.

| Результат | Статус | Что проверено | Что не проверено |
|---|---|---|---|
| APEX-PXP-1: `deg P_m ≤ 3m−2` для всех m (в препринте 2026-10-23 стоит `3m+2`) | PROVED (Lean), NEW_THEOREM_CANDIDATE | 2 веб-поиска 27.11.2026 (Fibonacci cube closed walks / PXP moments generating function) — совпадений не найдено | MathSciNet/zbMATH, OEIS-последовательности `Tr A_n^{2m}`, литература по кубическим многочленам Фибоначчиевых кубов (Klavžar, Mollard и др.) просмотрены не полностью |
| APEX-PXP-2: `P_m ≡ (2m)! z^{2m−1} mod (1−z−z²)`, знаменатель точен | PROVED (Lean), NEW_THEOREM_CANDIDATE | то же | то же; асимптотика `M_{m,n} ~ (2m)!/m!·φ^{2−m}5^{−(m+1)/2} n^m φ^n` могла встречаться в работах о спектре Фибоначчиевых кубов |
| APEX-PXP-3: `deg P_m = 3m−2` ровно, знак старшего коэффициента `(−1)^{m−1}` | PROVED (Lean), NEW_THEOREM_CANDIDATE | то же | то же |
| APEX-PXP-5: явные 4-й и 6-й моменты | PROVED (Lean), NEW_FORMALIZATION | совпадают с формулами препринта | — |
| Рациональность моментных рядов трансфер-матричными методами вообще | KNOWN_RESULT (в духе) | стандартная техника (комбинаторика, стат. механика) | — |

Источники поиска: arXiv 2601.17273 (Fibonacci-like cubes, не проверено подробно), arXiv 2502.07520 (Fibonacci p-cubes),
arXiv 1905.00573 (enumerative properties of Fibonacci-like cubes), arXiv 2112.06885 (hypergrid subgraphs, PXP scars).
Ни одна из них по аннотации не содержит утверждений о степени числителя моментных рядов. Следующий шаг: прочитать 2601.17273 и 1905.00573 целиком.

## Раунд 4 (27.11.2026)

Статусы по `APEX_CLAIMS.jsonl`; веб-поиск в этом раунде не проводился. Оценки ниже — от DISPROVER-агента и автора, не литературный обзор.

| Результат | Статус | Новизна |
|---|---|---|
| APEX-PXP-6: доказанный битовый DP для `Tr A_n^k` (все k) и `Σ Tr A_n^8 zⁿ = P₄/D⁵` | KERNEL_PROVED | NEW_FORMALIZATION (P₄ совпал с препринтом) |
| APEX-BLK-2: `Σ Tr A_{n,r}^2 zⁿ · D_r² = 2z` для всех r; тождества промежутков | KERNEL_PROVED | NEW_FORMALIZATION (второй момент = 2·число рёбер — элементарно) |
| APEX-BLK-3: корень ρ_r, минимальный модуль, `a_n ρⁿ → B_r(ρ)/K_r`, σ₁² = 1 − 1/√5 | KERNEL_PROVED | KNOWN_RESULT (теория линейных рекуррент), NEW_FORMALIZATION |
| APEX-BLK-4: знаменатель D_r^{m+1}, степень (2r+1)(m−1)+1, независимость старшего коэффициента от r, конгруэнция | NUMERICAL_EVIDENCE | NEW_THEOREM_CANDIDATE (требует доказательства и литературной проверки) |
| APEX-COL-1/2: no-go для log и высоты Цекендорфа; прирост 2 или 3 и точный счёт | KERNEL_PROVED | KNOWN_RESULT (фольклор), счёт — NEW_FORMALIZATION элементарного факта |
| APEX-ANY-1: braid-классификация 2×2, точная L2-норма дефекта | KERNEL_PROVED | KNOWN_RESULT (Rowell–Stong–Wang и др.), форма `(a−b)Q·C` — удобная переформулировка |
| APEX-S3-1: Фишер, dim H_n = (n+1)² | KERNEL_PROVED | KNOWN_RESULT, NEW_FORMALIZATION |
| APEX-SPC-1/2: спектральное препятствие (конечные меры), кумулянты 1–2 | KERNEL_PROVED | KNOWN_RESULT |
| APEX-NS-1: энергетическая оценка с силой (локальная по времени) | KERNEL_PROVED | KNOWN_RESULT |
| APEX-AKLT-1/2: ограничение на синглеты, код dim 3, QH₂P = QH₃P = 0; точная таблица утверждений | KERNEL_PROVED / NUMERICAL_EVIDENCE | NEW_FORMALIZATION; утверждения препринта верны только при прочтении A (формальные X_ij^k) |
| APEX-COS-1: ядро наблюдений на оболочках, неидентифицируемость | KERNEL_PROVED | KNOWN_RESULT (линейная алгебра) |
