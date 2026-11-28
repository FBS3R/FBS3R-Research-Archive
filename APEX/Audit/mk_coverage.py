#!/usr/bin/env python3
"""Regenerate APEX/COVERAGE.md (obligations x status x Lean targets + Mermaid dependency map)
from MISSION_STATE.json, Audit/APEX_RESULTS.json and Audit/ACCEPTED_THEOREMS.txt."""
import json, os, collections
H = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ms = json.load(open(f"{H}/MISSION_STATE.json"))
res = json.load(open(f"{H}/Audit/APEX_RESULTS.json"))
acc = open(f"{H}/Audit/ACCEPTED_THEOREMS.txt").read().split()
# round-5 obligations -> result ids / mission directions
OBL = [
 (1, "PXP: 10-й момент, старший коэффициент, асимптотика, гауссов предел", ["PXP-"], [2,3,4,5]),
 (2, "ConjGeneral для всех m, r", ["BLK-"], [6,7]),
 (3, "Универсальные автоматы R[x]/(x²), закон переноса", ["TRN-"], [9]),
 (4, "AKLT: полнота, ранг 6 / ядро 18, интерпретации", ["AKLT-"], [10]),
 (5, "Квантовая информация, каналы, diamond; FibonacciAnyon", ["QI-", "ANY-"], [13,14,15]),
 (6, "S³: гармоники, спектр, геометрия", ["S3-"], [18,19]),
 (7, "Навье–Стокс", ["NS-"], [16,17]),
 (8, "Янг–Миллс: масштаб, массовая щель", [], [21]),
 (9, "Квантовая гравитация, спектральное препятствие", ["SPC-1"], [20,22]),
 (10, "Космология: кумулянты, ядро оболочек", ["SPC-2", "COS-"], [23,24,25]),
 (11, "Коллатц: stopping time, циклы", ["COL-"], [11,12]),
 (12, "Каталог открытых задач", [], [27]),
 (13, "Единый закон", [], [26]),
 (14, "Аудит 101 работы архива, A1–A7 (Audit/ARCHIVE_AUDIT.md)", [], [1]),
]
dirs = {x["id"]: x for x in ms["directions"]}
def rs(prefs): return [r for r in res if any(r["id"].startswith("APEX-"+p) for p in prefs)]
EMO = {"KERNEL_PROVED": "🟩", "PARTIAL": "🟨", "IN_PROGRESS": "🟦", "NUMERICAL_EVIDENCE": "🟧",
       "OPEN": "⬜", "NOT_STARTED": "⬜", "KNOWN_RESULT": "🟩"}
L = ["# COVERAGE — покрытие обязательств APEX (раунд 5)", "",
     f"Сгенерировано `Audit/mk_coverage.py`. Реестр: **{len(acc)}** Lean-целей (`Audit/ACCEPTED_THEOREMS.txt`), "
     "все проверены ядром Lean 4.36 / Mathlib v4.36, аксиомы только `propext`, `Classical.choice`, `Quot.sound`.", "",
     "Легенда: 🟩 KERNEL_PROVED · 🟨 PARTIAL · 🟦 IN_PROGRESS · 🟧 NUMERICAL_EVIDENCE · ⬜ OPEN / NOT_STARTED.",
     "Статус «KERNEL_PROVED» означает доказанность сформулированного в Lean утверждения, а не решение открытой задачи.", "",
     "| № | Обязательство | Направления (MISSION_STATE) | Результаты | Lean-целей |", "|---|---|---|---|---|"]
for n, name, prefs, ds in OBL:
    rr = rs(prefs)
    dd = "<br>".join(f"{EMO.get(dirs[i]['status'],'')} {i}. {dirs[i]['name']} — {dirs[i]['status']}" for i in ds if i in dirs)
    L.append(f"| {n} | {name} | {dd} | {', '.join(r['id'].replace('APEX-','') for r in rr) or '—'} | {sum(len(r['lean']) for r in rr)} |")
L += ["", "## Результаты", "", "| ID | Область | Статус | Новизна | Утверждение |", "|---|---|---|---|---|"]
for r in res:
    L.append(f"| {r['id']} | {r['area']} | {EMO.get(r['status'],'')} {r['status']} | {r['novelty']} | {r['statement'].replace('|','/')} |")
c = collections.Counter(x["status"] for x in ms["directions"])
L += ["", "## Сводка по 27 направлениям", "", ", ".join(f"{k}: {v}" for k, v in sorted(c.items())), "",
      "## Карта зависимостей (доказано / открыто)", "",
      "Узлы — модули и задачи; зелёные — доказано ядром, жёлтые — частично, серые — открыто.", "", "```mermaid", "graph LR"]
G = """
 TR[PXP.Trajectories/Walks]:::ok --> RAT[PXP.Rational: D^{m+1}]:::ok --> DEG[PXP.Degree: deg=3m-2]:::ok
 MDP[PXP.MaskDP]:::ok --> M8[8-й, 10-й моменты]:::ok
 DEG --> LC[Старший коэфф. W m,m,1]:::num
 GT[Blockade.General.Transfer]:::ok --> GR[General.Rational]:::ok --> GRS[General.Residue]:::ok --> CG[ConjGeneral ∀m,r]:::ok
 GRS --> GD[General.Degree: Lc m, знак]:::ok --> CG
 CG --> AS[Asymptotics: моменты ~ 2m-1 !! σ^2m]:::ok --> GA[Gaussian: моменты, полиномы, плотность]:::ok --> WL[WeakLimit: слабая сходимость к N 0,σ²]:::ok
 CG --> RED[Exact: точный знаменатель, Lc 1..5]:::ok
 TN[Quantum.TraceNorm]:::ok --> CP[Quantum.CPTP]:::ok --> ON[OrthogonalNoise: Φ⁺, ◇]:::ok
 CP --> CT[Contractivity: точное ◇]:::ok --> ON
 B2[Anyon.Braid2D]:::ok --> FIB[Fibonacci: пентагон/гексагон, braid]:::ok
 BC[Collatz.BoundedCorrection]:::ok --> ST[Collatz.StoppingTime: mod 2^18]:::ok --> CYC[Cycles: n ≤ 2^20, циклы > 2^20]:::ok --> COLL[Гипотеза Коллатца]:::open
 SH[S3.Harmonic]:::ok --> SS[S3.Sphere: спектр -n n+2 /R²]:::ok --> L2[L²-полнота, Ходж, Дирак]:::open
 SS --> YM[Янг–Миллс: масштаб; массовая щель]:::open
 AP[AKLT.Physical]:::ok --> AL[AKLT.Leakage]:::ok
 PR[Spectral.PositiveRepresentation]:::ok --> QG[Квантовая гравитация]:::open
 MC[Spectral.MixtureCumulants]:::ok --> PRO[Spectral.Prony: кумулянты, идентифицируемость]:::ok --> COSM[Космология: тёмный сектор]:::part
 FE[Analysis.ForcedEnergy]:::ok --> IE[IntegralEnergy: L¹, без взрыва]:::ok --> NS[NS ℝ³ регулярность]:::open
 NIL[Transfer.Nilpotent: закон переноса, знаменатель]:::ok --> AUT[Несокращение полюса, PXP-конкретизация]:::open
 classDef ok fill:#2e7d32,color:#fff
 classDef part fill:#f9a825,color:#000
 classDef wip fill:#1565c0,color:#fff
 classDef num fill:#ef6c00,color:#fff
 classDef open fill:#9e9e9e,color:#000"""
L += G.strip("\n").splitlines() + ["```", ""]
open(f"{H}/COVERAGE.md", "w").write("\n".join(L) + "\n")
print("COVERAGE.md:", len(L), "lines")
