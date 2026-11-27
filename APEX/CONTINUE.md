# CONTINUE — как продолжить FBS3R–APEX

Последнее состояние: раунд 3 (27.11.2026), ветка `research/fbs3r-apex`, черновой PR #3. Состояние по направлениям: `MISSION_STATE.json`.

## Быстрый старт в новом контейнере
1. Lean 4.36.0 из GitHub releases (`lean-4.36.0-linux.tar.zst`, распаковка через python `zstandard`); кэш Mathlib в контейнере закрыт,
   поэтому Mathlib (fc4f59e5) собирается из исходников (≈45 мин на 4 ядрах). `lake update` зависает на кэше: прервать, запустить `lake build`.
2. `cd APEX/Lean && lake build && bash ../ci_check.sh` → должно напечатать `OK: 28 targets, standard axioms only`.
3. Сертификаты: `python3 -I APEX/Certificates/pxp_verify.py 15 4`, `python3 -I APEX/Certificates/blockade_verify.py 22 3`.
4. CI: `.github/workflows/apex-lean.yml` (elan + `lake exe cache get` + сборка + проверка аксиом).

## Правила
Без `sorry`/`admit`/`native_decide`/собственных аксиом; `#print axioms` для каждого главного результата; в `main` не сливать;
приоритет не заявлять без ядра Lean и проверки литературы; числовое подтверждение — это «гипотеза», а не теорема.

## Следующие шаги (по приоритету)
1. PXP M8: доказанный DP по спискам для `Tr Aₙ^8`, затем `decide +kernel` для n ≤ 10 → P₄ над D⁵.
2. Блокада радиуса r: перенести `Trajectories/Good` на совместимость «расстояние ≤ r» → знаменатель D_r^{m+1} для всех m.
3. Старший коэффициент W(m,m,1): 2, 4, 36, 568, 14560 — найти замкнутую форму и доказать (обобщить `GoodT`).
4. Асимптотика `Tr A_n^{2m} ~ (2m)! φ^{2−m} n^m φ^n /(m! 5^{(m+1)/2})` и гауссов предел N(0, 1−1/√5).
5. Поле μ (знаменатель D^{k+1}), AKLT 625, FibonacciAnyon, Навье–Стокс (энергетическая оценка с силой), гармоники S³.
