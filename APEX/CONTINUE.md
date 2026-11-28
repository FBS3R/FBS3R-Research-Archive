# CONTINUE — как продолжить FBS3R–APEX

Последнее состояние: раунд 5 (28.11.2026), ветка `research/fbs3r-apex`, черновой PR #3 (не сливать в main автоматически).
Состояние по 27 направлениям — `MISSION_STATE.json`; покрытие 14 обязательств раунда 5 и карта зависимостей — `COVERAGE.md`
(генерируется `python3 Audit/mk_coverage.py`); результаты — `Audit/APEX_RESULTS.json` / `Audit/APEX_CLAIMS.jsonl`;
реестр принятых теорем — `Audit/ACCEPTED_THEOREMS.txt` (221 цель на момент записи).

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

## В работе / следующие шаги
1. `Blockade/WeakLimit.lean` — слабая сходимость к N(0,σ_r²) (определённость гауссовой проблемы моментов).
2. `Quantum/Contractivity.lean` — сжимаемость следовой нормы, точное значение diamondDist для шумового канала.
3. `Anyon/Fibonacci.lean` — пентагон и гексагон.
4. Точный несократимый знаменатель (IsCoprime P D_r; случай r ≡ 4 mod 6); Lc(m) ядром для m ≤ 5.
5. Автоматы R[x]/(x²); S³: L²-полнота, Ходж; NS в L¹/AC-постановке; Коллатц: циклы; аудит 101 работы архива.
