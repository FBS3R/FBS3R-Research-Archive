# RED TEAM: независимая проверка PXP-результатов (раунд 1)

Проверку выполнял отдельный агент, который не писал доказательство и ничего не правил. Отчёт агента, 27.11.2026, кратко:

* **Целостность.** Все 6 модулей `APEX/PXP` перепроверены по отдельности (`lake env lean`): ошибок 0. `#print axioms` для
  `pxp_moment_rational`, `pxp_moment_residue`, `pxp_denominator_sharp`, `fourth_moment_gf`, `sixth_moment_gf` даёт только
  propext, Classical.choice, Quot.sound. Поиск по исходникам: нет sorry, admit, native_decide, axiom, unsafe, implemented_by, extern, opaque.
* **Определения.** `Legal` задаёт открытую цепочку. `Adj` (обе конфигурации допустимы и отличаются ровно в одном узле) совпадает
  с условием `P_{j−1}X_jP_{j+1}`. `M k n` — это буквально `Matrix.trace (adjMat n ^ k)`. Циклическое время `finRotate` встречается
  только во внутренней доказанной лемме. Крайние случаи: `A_0` — нулевая матрица 1×1, поэтому `M_{m,0}=0` (соглашение статьи); `Tr A_1² = 2`.
* **Непустота.** Значения, вычисленные ядром, совпадают с независимым Python-счётом агента: `Tr A_n²` для n = 0..4 равно 0, 2, 4, 10, 20;
  `Tr A_3⁴ = 42`; |Cfg 5| = 13. Матрица `adjMat` ненулевая, а `P` определяется однозначно, потому что `1−z−z²` обратим в `ℤ[[z]]`.
* **Ловушки.** Коэрсия Polynomial → PowerSeries — стандартный гомоморфизм колец. При m ≥ 1 вычитания `3m−2` и `2m−1` в ℕ корректны.
  Единственная гипотеза — m ≥ 1, как в статье. `pxp_denominator_sharp` верна для любого P, удовлетворяющего тождеству.
* **Сила границы.** Граница `3m−2` строже, чем `3m+2` в статье, и достигается при m = 1..4. Числитель при m = 4 совпадает с eq. (8th) статьи.

Вердикты:
1. `pxp_moment_rational` — ПРИНЯТО. Оговорка: точность границы (`deg P_m = 3m−2`) проверена только численно для m ≤ 4–5.
2. `pxp_moment_residue`, `pxp_denominator_sharp` — ПРИНЯТО.
3. `fourth_moment_gf`, `sixth_moment_gf` — ПРИНЯТО. Формула 8-го момента в Lean не формализована, она проверена только на Python.

## Раунд 3: независимый RED TEAM `Degree.lean` (27.11.2026, ревизия ca7daab)

Вердикт: **ACCEPT** (`APEX.PXP.pxp_numerator_natDegree`, `goodT_active`).

* `#print axioms`: только `propext`, `Classical.choice`, `Quot.sound`; в `Degree.lean` (333 строки) нет `sorry`, `admit`,
  `native_decide`, `axiom`, `unsafe`, `implemented_by`, `opaque`, `extern`.
* Сигнатура совпадает с заявлением; `M k n = trace(adjMat n ^ k)`, `adjMat` — куб Фибоначчи (строки без соседних единиц,
  смежность = отличие ровно в одном узле).
* `Special` не пуст: явный свидетель `β0 = ival(2m−2, 2m−1)`, `F = univ`; вычитания в ℕ (`3m−2`, `2j−2`, `2j−1`) защищены гипотезами.
* Независимая проверка на Python (точные числа замкнутых путей, n ≤ 18): степень 3m−2 и знак (−1)^{m−1} для m = 1..5;
  |старший коэффициент| = 2, 4, 36, 568, **14560** (m = 5 — новое значение, ещё не доказанное в Lean в общей форме).
* Оговорка (низкая): теорема условна по P; существование P даёт `pxp_moment_rational`.

## Раунд 4: независимый DISPROVER (27.11.2026, ревизия 4290944)

Проверено 8 модулей, 30 главных теорем; ни одна не опровергнута; ни одно утверждение не тривиализовано определениями.
Аксиомы у всех стандартные; гипотезы проверены на выполнимость (мера Дирака, x(t)=e^{−t}); Python-попытки опровержения
(Collatz n<20000, блокада r≤3 n<14, braid на 200 случайных комплексных точках, dim H_n при n≤8, ODE с кубическим A) — без контрпримеров.

| Модуль | Вердикт | Оговорка | Новизна |
|---|---|---|---|
| Collatz/BoundedCorrection, Collatz/Zeckendorf | ACCEPT | высота Цекендорфа ≈ log_φ n, по сути то же утверждение | KNOWN (фольклор), NEW_FORMALIZATION |
| Anyon/Braid2D | ACCEPT | только калибровка F=[[u,v],[v,−u]], диагональный R, вещественные u,v | KNOWN (Rowell–Stong–Wang и др.), NEW_FORMALIZATION |
| S3/Harmonic | ACCEPT-WITH-CAVEAT | над ℚ; `sphLap_of_harmonic` — только алгебраическое тождество, не спектр на S³ | KNOWN, NEW_FORMALIZATION |
| Spectral/PositiveRepresentation | ACCEPT-WITH-CAVEAT | только конечные меры (общий стилтьесовский случай не покрыт) | KNOWN, NEW_FORMALIZATION |
| Spectral/MixtureCumulants | ACCEPT | кумулянты порядка ≥ 3 не покрыты | KNOWN, NEW_FORMALIZATION |
| Analysis/ForcedEnergy | ACCEPT-WITH-CAVEAT | **решение предполагается дифференцируемым при всех t ∈ ℝ** (и назад во времени) — почти пусто для сильно диссипативных нелинейных A; исправление: локальная по времени версия (в работе) | KNOWN (энергетическая оценка), NEW_FORMALIZATION |
| Blockade/Count | ACCEPT | — | KNOWN (r=2: OEIS A000930), NEW_FORMALIZATION |

Вывод аудитора: все результаты раунда 4 — новые формализации известной или элементарной математики; новой математики среди них нет.

## Раунд 5: независимый DISPROVER (27.11.2026, ревизия 6282bb5)

| Модуль | Вердикт | Оговорка |
|---|---|---|
| Blockade/General/* (ConjGeneral для всех m, r) | ACCEPT | D_r приводим при r ≡ 4 (mod 6) (напр. 1−z−z⁵ = −(z²−z+1)(z³+z²−1)); «точный знаменатель» = следствие конгруэнции (z обратим по модулю каждого множителя ⇒ gcd(P, D_r) = 1), в Lean как отдельная теорема пока не сформулирован |
| PXP/ExplicitTenth | ACCEPT | таблицы создаются meta-командой через addDecl (данные), каждая перепроверяется ядром; поддельная таблица сломала бы доказательство |
| S3/Sphere | ACCEPT-WITH-CAVEAT | нет полноты гармоник в L², нет связи lapF с Mathlib `laplacian` |
| AKLT/Leakage | ACCEPT-WITH-CAVEAT | на синглетах N01=N23, N02=N13, N03=N12, поэтому 12 из 18 измерений ядра в интерпретации A — формальные избыточности; физичнее интерпретация B (ядро 19, образ 9) |

Численная проверка: brute-force для r ≤ 4, m ≤ 5: степени (2r+1)(m−1)+1 и старшие коэффициенты 2, −4, 36, −568, 14560 одинаковы для всех r.
Независимая рекурсия даёт Lc 6 = −546492 (новое значение, не проверено ядром). `#eval` Lean: Lc 1..3 = 2, −4, 36.
Новизна ConjGeneral: NEW_THEOREM_CANDIDATE (умеренная уверенность; поиск не исчерпывающий, нужна проверка специалистом).

## Round 5b — DISPROVER on the late round-5 modules (2026-11-28)

Scope: Quantum/{TraceNorm,CPTP,OrthogonalNoise,Contractivity}, Anyon/Fibonacci, Transfer/Nilpotent, Blockade/General/Exact,
Blockade/WeakLimit, Collatz/{StoppingTime,Cycles}, Analysis/IntegralEnergy; claims QI-1..4, ANY-2, TRN-1, BLK-9, BLK-10, COL-3, COL-4, NS-2.

* `#print axioms` on all 96 names: only propext / Classical.choice / Quot.sound. No forbidden tokens; `decide +kernel` only on
  Bool/ℕ/ℤ data and derived DecidableEq. Satisfiability instances compiled (`diamondDist_noisy_ideal_eq` at n = Fin 2, ι = Unit;
  `no_cancellation` at r = 4, m = 2).
* Independent Python checks: Fibonacci pentagon/hexagon (fail under perturbation, so not vacuous); blockade degree, Lc, gcd(P, D_r) = 1
  for (r,m) ∈ {(1,2),(2,2),(4,2),(10,2),(1,3),(4,3)}; Collatz counts k = 1..12, 7495 at k = 18, max Tt stopping time 183 below 2^20.
* Verdicts: **ACCEPT** QI-1, QI-2, QI-4, TRN-1, BLK-9, COL-3, NS-2; **ACCEPT_WITH_CAVEAT** QI-3 (state-input diamondDist, ancilla d,
  not identified with the standard ◇-norm), ANY-2 (Bonderson convention only up to R^{ab} = R^{ba}), BLK-10 (an immediate corollary of
  BLK-6; novelty relabelled COROLLARY_OF_BLK-6), COL-4 (requires 1 ≤ n). **REJECT: none.**
* Applied: registry wording fixes 1–7; stale "not proved" docstrings in OrthogonalNoise, CPTP and Gaussian updated (rebuild + gate OK, 287).
