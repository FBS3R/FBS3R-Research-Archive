# CONTINUE — как продолжить FBS3R–APEX

Последнее состояние: раунд 5 (28.11.2026), ветка `research/fbs3r-apex`, черновой PR #3 (не сливать в main автоматически).
Состояние по 27 направлениям — `MISSION_STATE.json`; покрытие 14 обязательств раунда 5 и карта зависимостей — `COVERAGE.md`
(генерируется `python3 Audit/mk_coverage.py`); результаты — `Audit/APEX_RESULTS.json` / `Audit/APEX_CLAIMS.jsonl`;
реестр принятых теорем — `Audit/ACCEPTED_THEOREMS.txt` (336 целей на момент записи).

## Быстрый старт
1. Lean 4.36.0 + Mathlib v4.36.0; кэш Mathlib в контейнере закрыт → `import Mathlib` целиком недоступен, только точечные импорты.
   В GitHub Actions кэш работает.
2. `cd APEX/Lean && lake build && cd ../.. && bash APEX/ci_check.sh` → `OK: N registered targets, standard axioms only, sources clean`.
   Новая теорема принимается, только если её имя есть и в `scripts/Axioms.lean`, и в `Audit/ACCEPTED_THEOREMS.txt`.
3. `python3 -I APEX/tests/test_cert_check.py` — отрицательные тесты гейта.
4. Сертификаты: `pxp_verify.py 15 4`, `blockade_verify.py 16 2`, `m8_walks.py`, `aklt_cert.py`.
5. Память: 15 ГБ на всё; не более 3–4 одновременных процессов Lean, `lake env lean -M 6000`. `Collatz/StoppingTime` ≈ 2–3 мин, ≈ 3.3 ГБ.

## Сделано в раунде 5
* 10-й момент PXP; `ConjGeneral` для всех m, r (`Blockade/General/*`); точная асимптотика и гауссовы моменты; спектральные меры:
  моменты, полиномы, плотность; AKLT (обе интерпретации); S³ спектр; квантовые каналы (следовая норма, Kraus, CP, нижняя оценка ◇);
  Коллатц: лемма Терраса и сертификаты mod 2^18 (KNOWN_RESULT, не доказательство гипотезы). DISPROVER раунда 5 — `Audit/RED_TEAM.md`.

## Также сделано в раунде 5 (поздние модули)
WeakLimit (слабая сходимость), Quantum/Contractivity (точное diamondDist), Anyon/Fibonacci, Transfer/Nilpotent, Blockade/General/Exact,
Collatz/Cycles, Analysis/IntegralEnergy, S3/Hopf, Spectral/Prony; аудит архива `Audit/ARCHIVE_AUDIT.md`; DISPROVER 5b без отказов.

## Следующие шаги
1. S³: L²-полнота гармоник, формы Ходжа, оператор Дирака, Максвелл (нужны модули Mathlib, не собранные локально — проверять в CI).
2. Связь diamondDist со стандартной ◇-нормой (Watrous 3.46/3.51); Choi–Kraus.
3. PXP/блокада: замкнутая формула Lc(m); Lc(6) ядром (≈1 ч, чанки).
4. Закон переноса: условия несокращения доминирующего полюса; конкретизация на PXP; поле μ.
5. Янг–Миллс, квантовая гравитация, Λ, единый закон, каталог открытых задач — открыты, честных теорем нет.
