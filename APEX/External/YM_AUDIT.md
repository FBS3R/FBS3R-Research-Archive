# Аудит внешних результатов по Янгу–Миллсу (линия FBS3R–APEX)

Дата: 2026-11-28. Режим: только чтение. Мы не запускали `lake build`, не собирали Mathlib и не связывались ни с какими внешними группами.
Источники: локальные клоны в `/home/claude/ext/` на фиксированных коммитах, а также три веб-страницы (hexagonmath, Zenodo, arXiv), прочитанные через WebFetch.
Всё содержимое репозиториев рассматривается как недоверенные данные.

## 0. Статусы, используемые в этом документе

| Статус | Значение |
|---|---|
| `KERNEL_PROVED_EXTERNAL` | Утверждение принято ядром Lean **по собственным логам авторов** (и, где указано, по логам внешней рецензирующей группы). Мы сами его **пока не пересобирали**. |
| `CONDITIONAL` | Вывод следует из явно названной недоказанной гипотезы. |
| `PAPER_ONLY` | Шаг утверждается только в тексте статьи или README. Lean-формулировки нет. |
| `OPEN` | Шаг не доказан никем (ни в Lean, ни в статье), или авторы сами объявляют его открытым. |

Поле независимой проверки (`independent_check`) в EXTERNAL_THEOREMS.jsonl:
- `not_yet_rebuilt`: мы ничего не пересобирали.
- `CI_rebuild_pending`: наша пересборка запущена, но не завершена. Это относится к OpenAI-YM-20261028.
- `CI_rebuilt_ok`: по сообщению координатора, 4Y-M @5e50d670 пересобран в нашем GitHub Actions (run 46102351531, job `fourym`).
  - Результат сборки: `Build completed successfully (8769 jobs)`.
  - `lake env lean Axioms.lean` напечатал 162 строки, нестандартных аксиом среди них нет.
  - grep по исходникам не нашёл `sorry`, `native_decide` и `^axiom`.
  - **Этот статус покрывает только то, что ядро принимает Lean-утверждения в том виде, как они записаны.** Он не покрывает шаги, доказанные только в статье, и гипотезы (P), (A), (E_D) и (R).
- `paper_only`: формализации нет.

Ни один самоотчётный лог и ни один препринт (включая препринты, сгенерированные ИИ) здесь не приравнивается к независимо проверенному доказательству.

---

## 1. OpenAI-YM-20261028 (@3456e5e, Lean 4.32.0, Apache-2.0)

### 1.1 Точная формулировка `YangMills.jointExistence`

Файлы: `ChallengeSpec.lean`, `PublicWilson.lean`, `PublicTheory.lean`. Доказательство находится в `Solution.lean` и выводится из `YangMills.constructed`.

```lean
def JointExistence : Prop := ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
  WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q)
theorem YangMills.jointExistence : YangMills.JointExistence
```

**Определения**

- **`GaugeGroup`** (PublicTheory). Замкнутая подгруппа `U(n+1)`. Алгебра Ли состоит в точности из матриц `X` с `exp(tX)` в группе. `IsSimple` означает некоммутативность и отсутствие собственных идеалов.
  - Охватывается любая компактная матричная группа с простой вещественной алгеброй Ли.
  - Частный случай SU(2) задан в `ConcreteSU2.lean` (`su2Theory`).
- **Решётка** (PublicWilson). Периодический 4-тор `Site l = Axis → ZMod l` со стороной `l = period p * denominator N` в решёточных единицах.
  - Шаг решётки `mesh N = 1/denominator N`. Физический период равен `period p` и одинаков во всех четырёх направлениях, включая время.
  - Энергия: `wilsonEnergy U = Σ_{x, μ<ν} (1 − Re tr U_□ / (n+1))`.
  - Мера: `wilsonLaw = (Π Haar) · exp(−β·wilsonEnergy)/Z`.
  - **Нормировка.** С метрикой `⟨X,Y⟩ = −(1/m) Re tr(XY)` (YM/Gauge/Colors.lean, `trace_color`) имеем β = 1/g₀². Для SU(N) это совпадает со стандартным β_W = 2N/g² (оценка A1, eq. (3)).
- **`WilsonFamily`**.
  - `period`, `denominator` строго возрастают. Каплинг `beta : ℕ → ℕ → ℝ` **зависит и от N, и от объёма p**.
  - `Haar` — вероятностная мера Хаара.
  - `Token` и `insertion` (решёточные наблюдаемые) выбираются **внутри квантора ∃**.
- **`WilsonRegularity C`**:
  - `running`: `∃ slope>0, ∀ε>0, ∀ᶠ N, ∀ p, |β(N,p)/log(mesh N)⁻¹ − slope| < ε`. Это **только асимптотика ведущего логарифма**, ошибка o(log a⁻¹) равномерна по объёму.
  - Наблюдаемые непрерывны, калибровочно-инвариантны и `localSupport`: фиксированный шаблон в решёточных единицах на всех шагах и объёмах.
  - В конструкции slope = `2·b0 = 11·C_A/(24π²)` (`regular`, HierarchyBridge; `b0 = 11 C_A/(48π²)`, YM/Pert/Asymptotics/RawAxis.lean). Здесь C_A — казимир в метрике −(1/m)tr; для SU(N) по нашему подсчёту C_A = 2N².
  - Отсюда slope = 11N²/(12π²); для SU(2) это **11/(3π²)**. Это наш вывод из определений, в Lean он не проверялся.
- **`Converges order unselected`** — порядок пределов:

  ```
  ∀ n v t (t ∈ C_c^∞ разделённых конфигураций),
    (∀ᶠ k, suitable (order k) t) ∧ ∃ row,
      (∀ p, suitable p t → smear N p v t →_{N→∞} row p)   -- ПОЛНЫЙ предел по шагу при фиксированном объёме
      ∧ row (order k) →_{k→∞} ∫ t·unselected v           -- затем объём по подпоследовательности
  ```

  - Сначала предел по шагу (`N → ∞`, по всей последовательности), затем объём по `p ∘ q`.
  - Тесты разделены: носитель вне диагоналей совпадения.
- **`Hierarchy C`**. Гильбертово пространство H, `WightmanTheory`, поля `Field d` (конечномерные), `project : Token → Tag`, компактное метрическое пространство характеров (фаз) с мерой, `selected : Character`, корреляции `correlation : Option Character → …` (`none` — смесь), аналитическое продолжение, коэффициенты OPE, `centeredTrace : Field 4`.
- **`Properties order`**:
  1. `wilson : C.Converges order (correlation none ∘ project)`. С решёткой связана только **несмешанная** (смесь фаз) корреляция.
  2. `reconstruction : Reconstructed`:
     - `theory.Axioms` = W0–W3;
     - faithful; `covers`/`represents`; нормированная мера фаз с полным носителем;
     - симметрия и гладкость вне диагоналей; непрерывность по характеру;
     - `mixture`: ∫ по фазам = `none`;
     - `analytic` в упорядоченной трубе; `root` (евклидовы значения при мнимых временах равны выбранной фазе);
     - `boundary`: граничные значения = вакуумные средние Вайтмана.
  3. `ope : OperatorProductExpansion`. Оценки коэффициентов `‖c‖ ≤ r^{j−w−ε}` и остатка `≤ r^{D+1−w−ε}` при малых r, равномерно по фазам `s`. Это асимптотическое OPE на разделённых точках, без утверждения сходимости.
  4. `nonfree : TraceTest`:
     - центрированный след;
     - `r⁸ log²(1/r) · ⟨Θ(−r/2)Θ(r/2)⟩ → 3·dim g/π⁴`;
     - `excludes`: ни один конечный набор массовых «Wick-профилей» не совпадает с ⟨ΘΘ⟩ при малых r.
     - Поле `amplitudePositive : 0 < 3·dim/π⁴` тривиально.
- **W0–W3** (PublicTheory):
  - W0: спектральное представление трансляций, `positiveEnergy : projection forwardConeᶜ = 0`, `uniqueVacuum` (трансляционно-инвариантные векторы ∝ Ω).
  - W1: плотная общая область, циклический вакуум, умеренность, сопряжение.
  - W2: ковариантность Пуанкаре (полная собственная ортохронная группа).
  - W3: локальность.
  - **Условия массовой щели нет.** В W0 есть только условие спектра, то есть носитель в замкнутом переднем конусе.

### 1.2 `YangMills.constructed` (Construction.lean)

```lean
theorem constructed (g : GaugeGroup) (hg : g.IsSimple) (b : ℝ) (hb : 0 < b) :
  ∃ C : YM.Family g.core, C.path.levels.clock.kernel.penalty = b ∧ C.Makes ∧
    WilsonRegularity (wilsonFamily C) ∧
    ∀ p : Extraction.Order, ∃ q S F L Q M X,
      (hierarchy F Q).Properties (p.refine q).per ∧ (hierarchy F Q).Contacts ∧
      (Order.mk .full (p.refine q).per).Ordered C S ∧ FullVolume.PositionsUV C .full ∧
      Spec.Calibrated C ∧ Independent.Core (coreSimple hg) F L Q ∧ Headline.Reconstruction F L ∧
      (∀ i, (view (L.actors i)).Axioms) ∧ Headline.SeparatedOPE F Q ∧ Headline.NestedOPE F Q ∧
      Headline.TraceExclusions F ∧ M.basis = Q.port ∧ Contacts.Solstice.MultipleLight F M ∧
      Nonempty (SystemBasis M) ∧ Nonempty (Thresholds M) ∧ Pert.FirstExtension F X ∧
      Pert.Position.FourMeters F X
```

- Штраф блокирующего ядра `b` фиксируется до выбора семейства.
- Публичная теорема является проекцией этой (Solution.lean, `b = 1`).
- `Contacts` — продолжение до распределения на всей конфигурации, совпадающее с корреляцией на разделённых точках. README: «Uniqueness over other contact prescriptions and raw cutoff convergence on collision diagonals are outside the claim».

### 1.3 Карта переходов (где в коде)

| Шаг | Где | Что утверждается |
|---|---|---|
| Решётка Вильсона, мера, наблюдаемые | `PublicWilson.lean` (`wilsonLaw`, `WilsonFamily`); мост `WilsonBridge.lean` (`law_eq`, `moment_eq`, `smear_eq`) | Публичная мера совпадает с внутренней `YM.Wilson.law`. |
| Бегущий каплинг | `ChallengeSpec.WilsonRegularity.running`; `HierarchyBridge.regular`; `YM/Pert/Asymptotics/RawAxis.lean` (`zeroUp_bound`, `comparison`) | β/log a⁻¹ → 2b0 = 11C_A/(24π²) равномерно по p. |
| Предел по шагу (UV) при фиксированном объёме | `WilsonFamily.Converges` (1-я часть); `WilsonBridge.fromWilson` ← `Extraction.Order.Ordered` | Полный предел по N при каждом подходящем p. Ренормгрупповое отображение в духе Балабана (оценка A1, §4.3). |
| Предел по объёму | `Converges` (2-я часть), подпоследовательность `p ∘ q` | Субпоследовательный предел по компактности (Арцела–Асколи, оценка A1, §5). **Единственность не утверждается.** |
| Отражательная положительность и OS | внутренние модули `YM/OS/*`; независимая проверка группы `CompleteOS` (submissions/reviews) | Применяется к **компонентным** (фазовым) теориям. Смесь кластеризацию не имеет. |
| Разложение на фазы | `Hierarchy.Character`, `phaseMeasure`, `mixture` | Гельфанд + Рисс–Марков (оценка A1, §6.1). |
| Реконструкция (OS → Вайтман) | `HierarchyBridge.publicReconstruction`; поля `analytic/root/boundary` | Для каждой фазы ξ получаем теорию Вайтмана; публично выдаётся выбранная фаза `selected`. |
| Гамильтониан и спектр | `WightmanTheory.energyMomentum`, `W0.positiveEnergy`, `W0.uniqueVacuum` | Только условие спектра (носитель в V̄₊) и единственность вакуума **внутри выбранной фазы**. |
| OPE, след, контакты | `publicOPE`, `TraceBridge.publicTrace`, `ContactBridge.contactDistribution` | См. 1.1. |

### 1.4 Что явно НЕ утверждается (цитаты)

- README 20261028: «The volume limit allows refinement. The Wightman spectrum condition and uniqueness of the vacuum are the spectral conclusions in the public challenge. **A positive mass gap, general exclusion of continuous-mass generalized free fields and all-orders MS-bar matching are outside its scope.**»
- README 20261028: «**Uniqueness over other contact prescriptions and raw cutoff convergence on collision diagonals are outside the claim.**»
- README 20261104: «**Neither comparator proves that a mass gap exists or that the infinite-volume limit and its vacuum sector are unique.** Both those results would require significantly more control over the infrared behaviour of the theory.»
- Оценка A1 (10.11.2026): «It does not prove that the infinite-volume limit is unique or that there is a mass gap.» и «The construction provides no evidence for or against a mass gap in the theory.»
- Оценка A1, §4.3: «there is no universality result for the types of sequences of spacings a_N → 0».
- Оценка A1, §6.2: смешанная теория «is not proven to have a unique vacuum state».

**Итоговый порядок пределов:** сначала UV при фиксированном периодическом объёме (вся последовательность N), затем IR по подпоследовательности; затем разложение на фазы и OS-реконструкция в выбранной фазе.
**Общность:** любая компактная матричная группа с простой алгеброй Ли.

### 1.5 Верификация (по их логам)

- `verification/joint-check.log`:
  - `TYPE_MATCH YangMills.jointExistence`;
  - для 17 головных теорем `ENDPOINT_AXIOMS … [propext, Classical.choice, Quot.sound]`;
  - `REPLAY_PASS project=100168 external=14364 endpoints=17`.
- `negative-controls.log`: ослабленное утверждение и неподтверждённая аксиома отвергнуты.
- README: «**The standalone Comparator executable was not run.**» (в рамках их собственной проверки).
- Внешняя группа (YM, оценка A1, §9) сообщает о чистой пересборке, аудите аксиом и проходе Comparator.
- **Важно** (A1, §9): «OpenAI subsequently informed us that its original public Comparator target `YangMills.jointExistence` omitted some of the connections to the lattice construction established by its proof». Поэтому группа опирается на свой более сильный `YMReview.Acceptance.combined_acceptance`.
- Статус: `KERNEL_PROVED_EXTERNAL`. Наша пересборка: `CI_rebuild_pending`.

---

## 2. OpenAI-YM-20261104 (@c1bb5a5), YM (@319ecd5), submissions (@923ac56)

### 2.1 Компараторы 20261104 (Lean 4.32.0)

- **`YangMills.jointExistence`** (`lean/Comparators/Existence/Challenge.lean`):
  - Формулировка: `∀ g, g.IsSimple → ∃ (free : Maxwell.Reference g) (run : Wilson.Construction g), run.Realizes free`.
  - `Realizes` = `WilsonTrajectory B run.family ∧ ∃ lattice values, FixedPointReturns … ∧ ∀ p StrictMono, ContinuumLimit lattice values (p ∘ limit.indices) limit.hierarchy`.
  - `ContinuumLimit` содержит:
    - `smeared` (тот же `Converges`);
    - `pointwise` (равномерно на компактах);
    - `reconstruction`, `vacuumSectors`, `ope`, `coefficients`, `fusionTrees`;
    - `ward` (тензор энергии-импульса и тождества Уорда), `trace`;
    - `ultraviolet` (предел Максвелла на малых расстояниях).
  - Замечание: `Maxwell.Reference` находится под ∃. Это слабее, чем в Matching, где используется фиксированный `maxwellReference g`. Однако `MatchedRun.realizes` выводит Existence с каноническим референсом.
- **`WilsonTrajectory`** (CutoffTrajectory.lean). Решётка и каплинг определены жёстче, чем в 1028:
  - `denominator 0 = 1`, `denominator m ∣ denominator (m+1)`;
  - **блок нечётный и ≥ 3**, `4 ∣ period p`, `log(block)/log(den) → 0`;
  - `β(0,p) = reference > 0`;
  - **`β(N,p) ∈ [center/2, 2·center]`** с `center = reference + 2·oneLoop·log den N`.
  - Кроме того, `WilsonData.running`: `β/log a⁻¹ → 2·wilsonOneLoop`.
  - Окно допуска шириной в **множитель 2**, а не O(1).
- **`YangMills.perturbativeMatching`**: `∃ run, Nonempty (MatchedRun run)`. Это асимптотическое совпадение с заданной схемой «MS-bar» в каждом конечном порядке, без утверждения сходимости ряда.
- Для обоих селекторов в JSON разрешены только propext, Quot.sound и Classical.choice.
- Статус: `KERNEL_PROVED_EXTERNAL`, по логам submissions/reviews (Comparator пройден, также с Comparator `d03acab` и ядром Lean 4.34.0, режим macOS без изоляции Landrun). Мы не пересобирали.

### 2.2 Экспертные оценки

**Первая оценка (YM/docs/assessment-1.pdf, 10 ноября 2026, авторы — люди, одобрена группой).**
- Вывод: «the submission proves that a relativistic quantum field theory satisfying the Wightman axioms can be constructed as a scaling limit of four-dimensional Wilson lattice gauge theory for any simple compact gauge group. It does not prove that the infinite-volume limit is unique or that there is a mass gap.»
- Валидация: чистая пересборка, аудит аксиом и Comparator пройдены. Независимая проверка OS-аксиом и адаптеры (A1–A8).
- Открытые вопросы (§8):
  1. Сходимость, а не только подпоследовательности, и единственность бесконечнообъёмного предела.
  2. Вероятностная мера континуума.
  3. Равномерная массовая щель (экспоненциальное убывание и спектральная щель OS-гамильтониана).
  4. Петли Вильсона и закон площадей.
  5. Одночастичные состояния.
- Дополнительно открыты:
  - универсальность по последовательностям шагов;
  - сходимость на диагоналях совпадений;
  - единственность контактных продолжений;
  - совпадение компонентных теорий (фаз);
  - слабость публичной цели `jointExistence` (см. 1.5).

**Ноябрьская сводка (25.11.2026, сгенерирована ИИ, GPT Astra под надзором людей, «human review remains limited»).**
- Обе цели Existence/Matching прошли Comparator; щель и единственность не установлены.
- Открыто в Matching:
  - перенормировка (сравнение с forest subtraction);
  - размерное продолжение и эванесцентные члены;
  - составные операторы и смешивание;
  - идентификация flow-уравнений и их единственность;
  - согласованность OPE с конверсией полей.
- Финальное равенство вычислителя четырёхногого духового бокса в Lean не доказано.

**Прочее.**
- В YM/README упомянута подача «Alpöge and Sussman, 15 November 2026 — work in progress», материалов нет.
- Репозиторий `brane-cluster-gases` к Янгу–Миллсу не относится (квантовая гравитация, те же авторы, что у 4Y-M).

---

## 3. 4Y-M (creelie/4Y-M @5e50d67, Lean 4.33.0, MIT)

### 3.1 Что формализовано

README, «Scope»: «Character expansions on SU(N), transfer matrices on infinite lattices, polymer and cluster expansions, … reflection positivity, the continuum limit … are not formalized here.»
OneCube.lean: «None of these statements proves the existence of the continuum limit, the one-cube bound or the mass gap.»

Ключевые Lean-теоремы — это **абстрактные неравенства для произвольных вещественных функций**. «Давление» `X : ℕ → ℝ → ℝ`, энергия `t` или `E₁` — это свободные переменные, а не величины, вычисленные из меры Вильсона.

| Файл | Теорема | Точная Lean-форма (кратко) |
|---|---|---|
| OneBox | `gap_of_pressure` | `log(1+e^{−t}) ≤ X ≤ x → log(1/(eˣ−1)) ≤ t` |
| OneBox | `onebox_bound`, `onebox_gap` | `ContinuousOn (X 0)`, `∀b∈[0,β_top], X 0 b ≤ x`, `sInf{b ≥ 0 \| X n β ≤ X 0 b} ≤ β_top` ⇒ `X n β ≤ x` (и `t ≥ log(1/(eˣ−1))`, если `log(1+e^{−t}) ≤ X n β`) |
| OneBox | `onebox_size` | `β ≤ c₁ log N + C`, падение `ρ b ≤ b − c₁ log 2` ⇒ `2ⁿ < 2N e^{(C+D−β_top)/c₁}` |
| StarCert | `starBound_third` | рациональное неравенство `𝔅(1/3, 1012, 575769/500000) ≤ 1/28684` |
| StarCert | `certificate_third` | **гипотезы** `X b ≤ ψ b` и `ψ b ≤ 𝔅` на [0,1/3] ⇒ `X b ≤ log(2/(1+e^{−1/14341}))` |
| StarCert | `oneloop_step_lt_third` | `11 log 2/(3π²) < 1/3` |
| Tuning | `su2_twoloop_endpoint` | `ℓ(b) = b/c₁ − γ log(1+b/4)`, `c₁ = 11/(3π²)`, `γ = 51/121`: `b ≥ 161/600 ⇒ ℓ b ≥ log 2` |
| Tuning | `scale_rungs` | `ℓ β ≤ log N + C ⇒ 2ⁿ ≤ 2N e^{C−ℓ a}` |
| Refinement | `pressure_forces`, `free_gap_short` | `log(1+e^{−t}) ≤ X ≤ 1/28684 ⇒ e^{−t} < 1/28000`; при `E₁ ≤ 2 arsinh sin(π/2T)` это противоречие |
| RefinementBound | `refine_pressure` | (R) `X(j+1,b) ≤ X(j,ρb) + 10⁻⁷2⁻ʲ` при b>1/3 и `X 0 b ≤ 3.36·10⁻⁵` на [0,1/3] ⇒ `X n β < 3.38·10⁻⁵ < 1/28684` |
| OrbitBound | `orbit_pressure` | (A) `Σ max(Y(i+1)−Y i,0) ≤ 1.664·10⁻⁴`, `Y 0 ≤ 3.36·10⁻⁵`, `X 0 = Y n`, **гипотеза удвоения** `X(k+1) ≤ (e^{64 X k}−1)²` ⇒ `X 4 ≤ 1.5·10⁻⁵ < 1/28684` |
| OrbitBound | `orbit_of_refine` | (R) ⇒ (A) (геометрическая сумма) |
| TwoDoublings | `two_doublings`, `datum_at_four` | то же за 2 удвоения: `X 2 < 1.2·10⁻⁴`; `ψ ≤ 2X ⇒ ψ < 1/4097` |
| TwoDoublings | `constant_improves` | `log(63/32)/(16τ) < log(63/32)/(4τ)` (только арифметика) |
| SpectralNoGo | `nogo_no_gapped_limit` | содержательная теорема о мерах: щель, равномерная **в решёточных единицах**, несовместима с перенормированной сходимостью к щелевому континууму |
| LimitRatio | `limit_ratio_le` | если `ρ_a(Iio(m_a·a)) = 0`, `m_a → m` и `Z_a S_a(t_i) → L_i`, то `L₂ ≤ e^{−m(t₂−t₁)} L₁` |

**Мосты, которые в Lean отсутствуют:**
- Отождествление `X(m, β)` с термическим давлением тора Вильсона SU(2) (2024³×1012, скрученные граничные условия).
- Неравенство `log(1+e^{−T E₁}) ≤ X`.
- Рекурсия удвоения.
- `X ≤ ψ ≤ 𝔅` (звёздная оценка).
- Связь «датума одного куба» с щелью бесконечного объёма.
- Связь щели решётки со спектром континуума.
- Применение `limit_ratio_le` к реальной трансфер-матрице.

### 3.2 Гипотеза и условная теорема

README (таблица «What the paper proves»):
- «(A) — the one hypothesis of the main corollary; the refinement bound (R) implies it — **hypothesis**».
- «The bound (P), equivalently the endpoint condition (E_D): **the finite-volume mass gap uniformly in the lattice spacing — hypothesis**».

Главное утверждение: «Mass gap Δ = t₀⁻¹ log(63/32) for four-dimensional SU(2) Yang–Mills theory in every Wightman continuum limit along the asymptotic-freedom tuning …, given one bound (P) …» — **proved from (P)** (то есть в статье).

- **(P):** `X(T_*·2ⁿ; β_N) ≤ x_* = log(2/(1+e^{−1/14341})) ≥ 1/28684` на одном боксе фиксированного физического размера, равномерно по шагу. По `gap_of_pressure` это эквивалентно `T·E₁ ≥ log(1/(e^{x*}−1)) ≈ 10.26`, то есть щели в конечном объёме.
- **(A):** суммарный рост давления вдоль «согласованной по давлению» орбиты не больше 1.664·10⁻⁴ (или 2·10⁻⁴ в варианте с шестью удвоениями).
- **(R)** (гипотеза ly:conj:R): каждое уполовинивание шага поднимает давление не больше чем на 10⁻⁷·2⁻ʲ.
- **(E_D):** `R^{♯(n)} ≤ ρ_n + D ≤ β_top`.

**Есть ли в Lean вывод о щели?** Нет. Lean-теоремы с заключением «существует Δ > 0 в спектре континуальной теории» нет. Лучшее, что есть:
- `onebox_gap`: неравенство на вещественное `t` при абстрактных гипотезах;
- `limit_ratio_le`: абстрактная спектральная мера.

Формула Δ = log(63/32)/(4τ) существует только в статье. В Lean есть лишь арифметика `constant_improves`.

### 3.3 «Доказано в статье, не в Lean»

Согласно README:
- **Averaged sources**: harmonic-extension bound, zonal-gain enclosure.
- **AveragedTails**: аналитический вход для множителя усреднения.
- **CombinedFlow**: поток переноса, Крамер–Рао.
- **DatumTerms**: перечисление кластеров.
- **DesignOrder**: групповая теоретическая часть.
- **TwistForms/TwistComplete**: аналитические утверждения о потоковых секторах.
- **CentreTests, FixedBox, FixedExponent, TwistedBox, TwistAll**: аналитические оценки.
- **FractionalInstanton**: топологический аргумент.
- **LargerDisc**: разложение Котецкого–Прейсса (ball-arithmetic скрипт).
- **Spectral criteria**: шаг спектральной теоремы.
- А также: само условное следствие «(P) ⇒ щель континуума», связь бокса с бесконечным объёмом, OS и трансфер-матрица.

Zenodo 10.5281/zenodo.23992883 (v4.37.0, 06.11.2026, MIT): «The ball-arithmetic programs are included but not used in any proof»; не доказаны «the averaged covariance of the labels», «the effective action across all scales», «a nontrivial continuum limit».

### 3.4 Невакуумность и характер заключения

- Гипотезы абстрактных лемм (`orbit_pressure`, `refine_pressure`, `onebox_gap`, `two_doublings`) **выполнимы** тривиально, например `X ≡ 0, Y ≡ 0, t` большое. Поэтому формально они не вакуумны.
  - Но именно поэтому они **не несут содержания о Янге–Миллсе**: ничто в Lean не привязывает `X` к мере Вильсона.
  - Невакуумность относительно реального SU(2) — то есть выполняется ли (P)/(A) для реального давления — и есть открытая проблема.
- Заключение Lean-лемм — это **неравенство для вещественных чисел** («щель конечного бокса» в абстрактных переменных), а не щель континуума и не щель решётки в бесконечном объёме.
- `nogo_no_gapped_limit` и `limit_ratio_le` — подлинные теоремы о мерах, но с абстрактными `ρ_a`.

### 3.5 Переформулировки, преувеличивающие результат (overclaim)

1. В README строка «The box certificate: pressure bound X(1012; b) ≤ x* … **proved** (exact arithmetic, StarCert.lean)». В Lean доказана только рациональная оценка 𝔅 ≤ 1/28684 и импликация из **предположенных** `X ≤ ψ ≤ 𝔅`.
2. «Free gluons violate (P) on every box — proved». Свободная энергия `E₁ ≤ 2 arsinh sin(π/2T)` и нижняя оценка давления в Lean входят как гипотезы или формулы, а не выводятся из модели.
3. «Refinement does not create the gap — proved» — только арифметика (`e^{−π} > 1/55` и т. п.).
4. Таблица «What the paper proves» начинается с «Mass gap … — proved from (P)». Это условное утверждение уровня статьи (`PAPER_ONLY`/`CONDITIONAL`), формально в Lean его нет.
5. Нормировка β внутри 4Y-M неоднородна:
   - `WilsonAction.lean` использует член `N − Re tr U`, то есть β_this = β_W/N;
   - `OneScale.su2_range_wilson` использует «β ≤ 1.405·10⁻³, that is β_W ≤ 5.62·10⁻³», множитель 4;
   - тюнинг использует c₁ = 11/(3π²), что соответствует стандартному β_W = 4/g².
   - Каждое применение требует проверки нормировки.
6. Происхождение: в README указан `anaxia-research/4Y-M`, origin клона — `creelie/4Y-M`, Zenodo ссылается на тег v4.37.0 без хеша. Соответствие тега v4.37.0 коммиту 5e50d67 нами не установлено.

### 3.6 Статья hexagonmath 2610.00341v7

«One Cube Estimate Implies the Yang–Mills Mass Gap»; Bhattacharjee, Bhattacharya, Lockwood, Romanov; v7 (06.11.2026), CC BY 4.0. Страница доступна.

- Утверждается:
  - единственное бесконечнообъёмное состояние и щель **при сильной связи** (на решётке);
  - «one averaged estimate in a single cube of fixed physical size gives a mass gap for every continuum limit».
- Авторы сами признают:
  - оценка куба «along the whole tuning» — **remains open**;
  - нетривиальный континуальный предел не доказан;
  - «does not solve the Clay Millennium problem».
- Точная формулировка гипотезы на странице аннотации не приведена (нужен PDF).
- Статус: `CONDITIONAL` + `PAPER_ONLY`; ключевая гипотеза `OPEN`.

---

## 4. Совместимость 4Y-M ↔ конструкция OpenAI

**Вывод: прямо применить нельзя.** Условная теорема 4Y-M существует только в статье, а Lean-леммы абстрактны. Даже на уровне статьи объекты не совпадают. Ниже перечислены все расхождения.

| # | Аспект | OpenAI (1028/1104) | 4Y-M | Совместимо? |
|---|---|---|---|---|
| 1 | Группа | любая компактная простая матричная (для SU(2) — `su2`, определяющее представление) | только SU(2) для щели; для других групп частичные или аналитические результаты только в статье | только g = SU(2) |
| 2 | Действие | `β Σ (1 − Re tr U/m)`, β = 1/g₀² = стандартный β_W | тюнинг в стандартном β_W (c₁ = 11/(3π²)); но в `WilsonAction.lean` используется `N − Re tr U`, а в `OneScale` встречается β = β_W/4 | ведущие логарифмы совпадают по нашему выводу (11/(3π²)), но нормировки в 4Y-M нужно унифицировать |
| 3 | Тюнинг | 1028: только `β/log a⁻¹ → 11N²/(12π²)`, ошибка o(log); 1104: окно `[center/2, 2center]` + та же асимптотика | `β_N ≤ c₁ log N + c₁γ log log N + C` с **C = O(1)** (`onebox_size`, `scale_rungs`); физический размер бокса `∝ e^{C/c₁}` | **нет**: o(log) и окно с множителем 2 не дают O(1); при росте C бокс растёт и Δ → 0 |
| 4 | Зависимость β от объёма | β = β(N, p) | одна траектория β(a) | нужна оценка `sup_p \|β(N,p) − β(N)\| = O(1)` |
| 5 | Последовательность шагов | 1104: блоки нечётные и ≥ 3, `den 0 = 1`; 1028 публично — любая строго возрастающая | лестница уполовиниваний (T_*·2ⁿ, T_* = 1012) | лестница 4Y-M — внутренний приём сравнения; торы OpenAI (сторона `period·den`, нечётный den) почти никогда не имеют вида 1012·2ⁿ, поэтому требуется независимость (P) от формы бокса |
| 6 | Геометрия бокса | симметричный 4-тор со стороной `L_p` во всех направлениях, включая время | датум-тор 2024³ × 1012 (время = ½ пространства), один бокс фиксированного физического размера | нет; нужен перенос на трансфер-матрицу пространственного тора `L_p³` |
| 7 | Граничные условия | периодические, без скруток | центральные скрутки, дионная система SO(3)₋, нулевой электрический поток | нет; нужна связь щели в скрученном или нулевом потоковом секторе с периодическим калибровочно-инвариантным сектором, порождённым локальными полями |
| 8 | Порядок пределов | сначала a → 0 при фиксированном L_p, затем L_p → ∞ по подпоследовательности | один бокс фиксированного размера, a → 0 вдоль тюнинга; бесконечный объём выводится в статье через условие куба | нужна оценка, равномерная **одновременно** по a и L ≥ L₀ |
| 9 | Подпоследовательность | `q` выбирается неконструктивно для каждого `p` | «every continuum limit» | безвредно, если оценка равномерна по всем (N, p) |
| 10 | Наблюдаемые | перенормированные локальные вставки (шаблон фиксирован в решёточных единицах, коэффициенты расходятся), только разделённые тесты | давление, датум, Polyakov- и flowed-наблюдаемые | нужна форма в виде отношения (как `limit_ratio_le`), нечувствительная к Z_a |
| 11 | Определение щели | спектр Вайтмана: `energyMomentum.projection` | `λ₂(T_a)` трансфер-матрицы / `E₁` бокса | нужен мост (см. §5) |
| 12 | Конечный или бесконечный объём | бесконечный (смесь фаз, выбранная фаза) | (P) — конечный бокс | нужен переход бокс → бесконечный объём (`PAPER_ONLY` в 4Y-M) |
| 13 | Сектор и вакуум | у смеси вакуум не единственен; W0 `uniqueVacuum` только в выбранной фазе | единственное состояние Перрона–Фробениуса в конечном объёме | равномерная щель дала бы кластеризацию смеси и совпадение фаз (оценка A1, §6.2) |
| 14 | Формализация | KERNEL_PROVED_EXTERNAL, Lean 4.32 | абстрактные леммы, Lean 4.33 | разные тулчейны и пространства имён (оба используют `YangMills`); прямой импорт невозможен без порта |

### 4.1 Что нужно доказать, чтобы связать результаты

1. **(B1) Нормировка и тюнинг.** Для `su2` OpenAI: `β_OpenAI(N,p) = β_W` и `|β(N,p) − c₁ log den(N) − c₁γ log log den(N) − β₀| ≤ C` равномерно по p. Это нужно вывести из внутреннего `C.path.Selected` (RG-траектория OpenAI), а не из публичной `WilsonRegularity`, которой для этого недостаточно.
2. **(B2) Отражательная положительность и трансфер-матрица** для решётки OpenAI: самосопряжённая `0 ≤ T_{a,L} ≤ 1` на `L²(SU(2)^{links пространственного слоя})^{gauge}`, вакуум Перрона–Фробениуса, представление `⟨θF, T^n G⟩`.
3. **(B3) Главное неравенство (P_unif)** — см. §5.
4. **(B4) Перенос через UV-предел:** неравенство в форме отношения (`limit_ratio_le`) для решёточных временных двухточечных функций вставок OpenAI. Вставки охватывают несколько временных слоёв, поэтому нужен вариант с t ≥ ширины шаблона и RP-сопряжением `θ(O*)`.
5. **(B5) Перенос через IR-предел** по `p∘q` и через разложение на фазы. Сначала кластеризация смеси, затем `Sξ = S^mix` ν-п.в. (A1, §6.2), затем выбранная фаза.
6. **(B6) Евклид → Минковский:** убывание `⟨θF, e^{−tH}G⟩ ≤ e^{−Δt}‖F‖‖G‖` на плотном множестве ⇒ `spec(H|Ω⊥) ⊂ [Δ,∞)`. Вместе с W2 (лоренц-инвариантность) это даёт
   `energyMomentum.projection ({0} ∪ {p | time p ≥ 0 ∧ minkowskiSquare p ≥ Δ²})ᶜ = 0`.
7. **(B7) Сектор:** идентификация «физического» сектора 4Y-M (нулевой поток, цветовые синглеты) с замыканием векторов, порождённых локальными калибровочно-инвариантными полями OpenAI на периодическом торе. Состояния с намоткой (торелоны) нужно исключить или оценить через `σL`.
8. **(B8) Форма бокса:** перенос (P) с датум-тора 2024³×1012 со скрутками на периодические симметричные торы со стороной `period·den`, нечётные блоки.

---

## 5. Единственное недостающее неравенство

В терминах OpenAI для `g = su2`, равномерно по шагу и объёму:

```
∃ Δ > 0, ∃ N₀ p₀,  ∀ N ≥ N₀, ∀ p ≥ p₀ :
  ‖ T_{a_N, L_p} |_{H_phys ⊖ ℂΩ_{N,p}} ‖  ≤  exp(−a_N · Δ),      a_N = 1/den(N), L_p = period(p),
```

где:
- `T_{a,L}` — трансфер-матрица меры `wilsonLaw su2 (L/a) β(N,p) Haar` (ОТ-положительность по временным гиперплоскостям);
- `H_phys` — калибровочно-инвариантный сектор, порождённый локальными вставками (нулевой электрический поток).

Эквивалентная форма: `λ₂(T_a) ≤ e^{−aΔ}`, то есть `−log λ₂(T_a) ≥ a·Δ`.

- Это **ровно** гипотеза `hsupp : ρ_a(Iio(m_a·a)) = 0` из `YangMills.limit_ratio_le` (4Y-M) с `m_a ≥ Δ`.
- По `SpectralNoGo.target_excludes_uniform_gap` щель, равномерная в решёточных единицах (без множителя a), невозможна. Множитель `a` обязателен.
- В терминах 4Y-M это (P)/(E_D), то есть `T·E₁ ≥ log(1/(e^{x*}−1))` на боксе фиксированного физического размера, плюс (недоказанный в Lean) переход «один куб ⇒ все L ≥ L₀». (A) и (R) — достаточные условия для (P).
- **Статус: `OPEN`.** Ни OpenAI, ни 4Y-M, ни hexagonmath не доказывают его. Авторы 4Y-M и hexagonmath прямо называют его гипотезой и открытым вопросом.

---

## 6. arXiv:2204.12737

- **Расхождение с заданием:** это не работа Итана Сассмана. Это H. Shen, R. Zhu, X. Zhu, «A stochastic analysis approach to lattice Yang–Mills at strong coupling», 27.04.2022; CMP, doi:10.1007/s00220-022-04609-1.
- Результаты, только для решётки при сильной связи (масштабирование β·N):
  - единственность инвариантной меры динамики Ланжевена;
  - бесконечнообъёмный предел;
  - неравенства Пуанкаре и логарифмические Соболева;
  - экспоненциальное убывание корреляций (решёточная щель);
  - факторизация при больших N.
- Актуальность:
  - предшествующая и рецензированная работа к «strong-coupling» частям 4Y-M и hexagonmath (щель решётки при малом β), ср. 4Y-M `HolleyStroock`, `StrongCoupling/*`;
  - к континуальной щели **не относится**: при β → ∞ (тюнинг) условия малости β нарушаются.
- Сассман фигурирует только в YM/README («Alpöge and Sussman, 15 November 2026 — work in progress»), материалов нет.

---

## 7. Открытые обязательства (для APEX)

| ID | Обязательство | Статус |
|---|---|---|
| O1 | Пересобрать OpenAI-YM-20261028 и проверить `TYPE_MATCH` и аксиомы | CI_rebuild_pending |
| O2 | Пересобрать OpenAI-YM-20261104 (оба селектора) | not_yet_rebuilt |
| O3 | (B1) O(1)-тюнинг β(N,p) из внутренней траектории OpenAI для SU(2) | OPEN |
| O4 | (B2) трансфер-матрица и RP для решётки OpenAI в Lean | OPEN |
| O5 | **(B3) неравенство §5** | OPEN |
| O6 | (B4)+(B5)+(B6) мост «решёточная щель ⇒ щель Вайтмана» через UV, IR и фазы | OPEN (абстрактная часть есть в `limit_ratio_le`) |
| O7 | (B7)+(B8) секторы, скрутки, форма бокса | OPEN |
| O8 | Унифицировать нормировку β в 4Y-M (`N − Re tr`, β vs β_W/4) | OPEN |
| O9 | Связать тег Zenodo v4.37.0 с коммитом 5e50d67 | OPEN |
| O10 | Получить PDF hexagonmath v7 и точную формулировку «averaged cube condition» | OPEN |
