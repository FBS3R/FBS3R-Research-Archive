# CONTINUE — как продолжить FBS3R–APEX

Последнее состояние: раунд 4 (27.11.2026), ветка `research/fbs3r-apex`, черновой PR #3. Состояние по 27 направлениям — `MISSION_STATE.json`,
результаты — `Audit/APEX_RESULTS.json` / `Audit/APEX_CLAIMS.jsonl`, реестр принятых теорем — `Audit/ACCEPTED_THEOREMS.txt` (137 целей).

## Быстрый старт
1. Lean 4.36.0 (GitHub releases, распаковка python `zstandard`); кэш Mathlib в контейнере закрыт → сборка Mathlib из исходников.
   В GitHub Actions кэш работает (сборка ≈ 3–10 мин).
2. `cd APEX/Lean && lake build && cd ../.. && bash APEX/ci_check.sh` → `OK: 137 registered targets, standard axioms only, sources clean`.
   Новая теорема принимается, только если её имя есть и в `scripts/Axioms.lean`, и в `Audit/ACCEPTED_THEOREMS.txt` (иначе гейт падает).
3. `python3 -I APEX/tests/test_cert_check.py` — отрицательные тесты гейта.
4. Сертификаты: `pxp_verify.py 15 4`, `blockade_verify.py 16 2` (большой: `22 3`), `m8_walks.py`, `aklt_cert.py`.
5. LaTeX: `apt-get update && apt-get install texlive-latex-extra texlive-science lmodern`; PDF статей лежат в `Manuscripts/`.

## Прервано на середине
* **10-й момент PXP** (`WIP/ExplicitTenth.lean.wip`, НЕ принят, не проверен): план — `MaskDP.M_eq_Mnat` + `decide +kernel` для k=10, n ≤ 13,
  по одному n на лемму; следить за памятью (OOM при 15 ГБ на всех). Ожидание: старший коэффициент P₅ = +14560, P₅ ≡ 10! z⁹ mod D.

## Следующие шаги
1. Блокада: `ConjGeneral` (Moments.lean) — общий m через перенос Good/GoodR/GoodT на r соседей; 2-й и 4-й моменты уже доказаны для всех r.
2. Гауссов предел: асимптотика моментов из рациональности + `Root.lean`, затем метод моментов.
3. Квантовые каналы (TraceNorm/CPTP/диамантовая норма) — инфраструктуры в Mathlib нет; начать с норм Шаттена.
4. S³: полярное разложение и спектр на сфере; масштабирование Янга–Миллса R⁻².
5. Автоматы R[x]/(x²), поле μ; FibonacciAnyon пентагон/гексагон; Коллатц stopping-time; каталог открытых задач.
