# COVERAGE — покрытие обязательств APEX (раунд 5)

Сгенерировано `Audit/mk_coverage.py`. Реестр: **221** Lean-целей (`Audit/ACCEPTED_THEOREMS.txt`), все проверены ядром Lean 4.36 / Mathlib v4.36, аксиомы только `propext`, `Classical.choice`, `Quot.sound`.

Легенда: 🟩 KERNEL_PROVED · 🟨 PARTIAL · 🟦 IN_PROGRESS · 🟧 NUMERICAL_EVIDENCE · ⬜ OPEN / NOT_STARTED.
Статус «KERNEL_PROVED» означает доказанность сформулированного в Lean утверждения, а не решение открытой задачи.

| № | Обязательство | Направления (MISSION_STATE) | Результаты | Lean-целей |
|---|---|---|---|---|
| 1 | PXP: 10-й момент, старший коэффициент, асимптотика, гауссов предел | 🟩 2. PXP рациональная иерархия (deg=3m−2, вычет, знак) — KERNEL_PROVED<br>🟩 3. PXP 8-й момент (доказанный DP) — KERNEL_PROVED<br>🟧 4. PXP старший коэффициент W(m,m,1) — NUMERICAL_EVIDENCE<br>🟩 5. PXP/блокада: асимптотика и гауссов предел — KERNEL_PROVED | PXP-1, PXP-2, PXP-3, PXP-5, PXP-6, PXP-7 | 10 |
| 2 | ConjGeneral для всех m, r | 🟩 6. Блокада r: размерности — KERNEL_PROVED<br>🟩 7. Блокада r: моменты, D_r^{m+1}, степень, конгруэнция — KERNEL_PROVED | BLK-1, BLK-2, BLK-2b, BLK-3, BLK-4, BLK-5, BLK-6, BLK-7, BLK-8, BLK-9 | 27 |
| 3 | Универсальные автоматы R[x]/(x²), закон переноса | ⬜ 9. Общий закон переноса для автоматов (R[x]/(x²)) — OPEN | — | 0 |
| 4 | AKLT: полнота, ранг 6 / ядро 18, интерпретации | 🟩 10. AKLT 625: физическая карта утечки — KERNEL_PROVED | AKLT-1, AKLT-2, AKLT-3 | 11 |
| 5 | Квантовая информация, каналы, diamond; FibonacciAnyon | 🟩 13. FibonacciAnyon: braid-классификация 2×2, норма дефекта — KERNEL_PROVED<br>🟦 14. FibonacciAnyon: пентагон, гексагон, универсальность — IN_PROGRESS<br>🟨 15. Квантовые каналы, алмазная норма (BINDU VECTRA) — PARTIAL | ANY-1, QI-1, QI-2, QI-3 | 22 |
| 6 | S³: гармоники, спектр, геометрия | 🟩 18. S³: гармонические многочлены, Фишер, dim (n+1)² — KERNEL_PROVED<br>⬜ 19. S³: риманова геометрия, Ходж, Дирак — NOT_STARTED | S3-1, S3-2 | 8 |
| 7 | Навье–Стокс | 🟩 16. Навье–Стокс: энергетическая оценка с силой (конечномерная) — KERNEL_PROVED<br>⬜ 17. Навье–Стокс: регулярность в ℝ³ — OPEN | NS-1 | 2 |
| 8 | Янг–Миллс: масштаб, массовая щель | ⬜ 21. Янга–Миллса: масштабирование λ(R)=R⁻²λ(1), массовая щель — OPEN | — | 0 |
| 9 | Квантовая гравитация, спектральное препятствие | 🟩 20. Спектральное препятствие exp(−ax)/x — KERNEL_PROVED<br>⬜ 22. Квантовая гравитация (Fractal Foliation, CMC, связи, унитарность) — OPEN | SPC-1 | 2 |
| 10 | Космология: кумулянты, ядро оболочек | 🟨 23. Топология Вселенной, идентифицируемость (S³, RP³, S³/Γ) — PARTIAL<br>⬜ 24. Космологическая постоянная Λ=3π/(ℓ_P² q), выбор q — OPEN<br>🟨 25. Тёмный сектор, кумулянты смесей — PARTIAL | SPC-2, COS-1 | 7 |
| 11 | Коллатц: stopping time, циклы | 🟩 11. Коллатц: no-go ограниченной поправки (log и высота Цекендорфа) — KERNEL_PROVED<br>🟨 12. Коллатц: stopping-time сертификаты, циклы, 2-адика — PARTIAL | COL-1, COL-2, COL-3 | 12 |
| 12 | Каталог открытых задач | ⬜ 27. Каталог открытых задач (Риман, P vs NP, Ходж, BSD, MLC, Гольдбах, близнецы, совершенные, Эрдёш, Рамсей) — OPEN | — | 0 |
| 13 | Единый закон | ⬜ 26. Причинность, свет, единый закон — OPEN | — | 0 |
| 14 | Аудит 101 работы архива, A1–A7 | 🟨 1. Аудит/CI/сертификация — PARTIAL | — | 0 |

## Результаты

| ID | Область | Статус | Новизна | Утверждение |
|---|---|---|---|---|
| APEX-PXP-1 | PXP | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | sum_n Tr A_n^{2m} z^n (1-z-z^2)^{m+1} = P_m in Z[z], deg <= 3m-2, all m>=1 |
| APEX-PXP-2 | PXP | 🟩 KERNEL_PROVED | NEW_THEOREM_CANDIDATE | P_m = (2m)! z^{2m-1} mod D; denominator sharp |
| APEX-PXP-3 | PXP | 🟩 KERNEL_PROVED | NEW_THEOREM_CANDIDATE | deg P_m = 3m-2 exactly, top coefficient sign (-1)^{m-1} |
| APEX-PXP-5 | PXP | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | explicit 4th and 6th moment GFs |
| APEX-PXP-6 | PXP | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | proved bit-mask DP for Tr A_n^k (all k); sum Tr A_n^8 z^n = P_4/D^5 |
| APEX-BLK-1 | Blockade | 🟩 KERNEL_PROVED | KNOWN_RESULT | a_n = a_{n-1} + a_{n-r-1}; GF B_r/D_r |
| APEX-BLK-2 | Blockade | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | sum Tr A_{n,r}^2 z^n * D_r^2 = 2z for all r; gap identities D_r S_r + z^r B_r = 1 |
| APEX-BLK-2b | Blockade | 🟩 KERNEL_PROVED | NEW_THEOREM_CANDIDATE | for all r: sum Tr A_{n,r}^4 z^n * D_r^3 = 2z D_r + 4z^2(1+..+z^{r-1}) D_r + 24 z^{r+2} |
| APEX-BLK-3 | Blockade | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | rho_r unique simple root of minimal modulus; B_r(rho)=rho^-r; a_n rho^n -> B_r(rho)/K_r; sigma_1^2 = 1-1/sqrt5 |
| APEX-BLK-4 | Blockade | 🟩 KERNEL_PROVED | NEW_THEOREM_CANDIDATE | superseded by APEX-BLK-5/6/7 (all proved) |
| APEX-COL-1 | Collatz | 🟩 KERNEL_PROVED | KNOWN_RESULT | no bounded correction for log or Zeckendorf height along the Syracuse map |
| APEX-COL-2 | Collatz | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | h(3n+1)-h(n) in {2,3}; exact count of gain 3 per Fibonacci layer |
| APEX-ANY-1 | Anyon | 🟩 KERNEL_PROVED | KNOWN_RESULT | RBR-BRB=(a-b)Q C; classification; cos th = 1-1/(2u^2); exact L2 defect norm |
| APEX-S3-1 | S3 | 🟩 KERNEL_PROVED | KNOWN_RESULT | Fischer decomposition over Q, dim H_n=(n+1)^2; algebraic spherical-Laplacian identity (sphere spectrum not yet) |
| APEX-SPC-1 | Spectral | 🟩 KERNEL_PROVED | KNOWN_RESULT | finite positive spectral measures: xG(x) -> rho([0,inf)); exp(-ax)/x excluded |
| APEX-SPC-2 | Spectral | 🟩 KERNEL_PROVED | KNOWN_RESULT | first two cumulants of positive mixtures; log-MGF identity |
| APEX-NS-1 | Analysis | 🟩 KERNEL_PROVED | KNOWN_RESULT | finite-dim energy bound with forcing, local in time; not a Navier-Stokes regularity result |
| APEX-AKLT-1 | AKLT | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | singlet restriction, code dim 3 (within the 5 explicit singlets), Q H2 P = Q H3 P = 0 |
| APEX-AKLT-2 | AKLT | 🟧 NUMERICAL_EVIDENCE | NEW_FORMALIZATION | exact-rational: leakage rank 6, ker 18, logical image 4, degrees 1..4 -> 1..4, u(2)+u(1) under interpretation A (formal X_ij^k); under the generated-algebra reading ker 19 and image 9 — rank/kernel/image now KERNEL_PROVED (AKLT-3); per-degree dims and Lie algebra still Python-only |
| APEX-COS-1 | Cosmology | 🟩 KERNEL_PROVED | KNOWN_RESULT | shell observation kernel = nodal multiples, dim d+1-q, reconstruction iff q>=d+1; local non-identifiability of positive parameters |
| APEX-PXP-7 | PXP | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | sum Tr A_n^10 z^n = P_5/D^6, top coefficient 14560; kernel-checked checkpoint tables generated by meta code (addDecl, kernel-verified) |
| APEX-BLK-5 | Blockade | 🟩 KERNEL_PROVED | NEW_THEOREM_CANDIDATE | for all r,m>=1: sum Tr A_{n,r}^{2m} z^n * D_r^{m+1} = P with deg P <= (2r+1)(m-1)+1 |
| APEX-BLK-6 | Blockade | 🟩 KERNEL_PROVED | NEW_THEOREM_CANDIDATE | for all r,m>=1: P = (2m)! z^{(r+1)m-r} mod D_r (hence denominator exact) |
| APEX-S3-2 | S3 | 🟩 KERNEL_PROVED | KNOWN_RESULT | over R: dim H_n=(n+1)^2; Laplacian of degree-0 extension on S_R gives -n(n+2)/R^2; geometric eigenvalues scale R^-2 -> 0 |
| APEX-BLK-7 | Blockade | 🟩 KERNEL_PROVED | NEW_THEOREM_CANDIDATE | ConjGeneral for all m,r>=1: deg P_{m,r} = (2r+1)(m-1)+1 exactly, leading coefficient Lc m independent of r with sign (-1)^{m-1}, and D_r / P - (2m)! z^{(r+1)m-r} |
| APEX-AKLT-3 | AKLT | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | singlet space = span of 5 explicit vectors (rank 5); interpretation A (formal X_ij^k): leakage rank 6, kernel 18, logical image 4; interpretation B (generated algebra = M_5): kernel 19, logical image gl(3) |
| APEX-BLK-8 | Blockade | 🟩 KERNEL_PROVED | NEW_THEOREM_CANDIDATE | for all r,m>=1: Tr A_{n,r}^{2m} rho^n/n^m -> (2m)! rho^{(r+1)m-r}/(m! K_r^{m+1}); normalised moments Tr A^{2m}/(a_n n^m) -> (2m-1)!! sigma_r^{2m} (Gaussian moments, sigma_r^2 = 2 rho^{r+1}/K_r); odd moments vanish. Weak convergence of spectral measures not yet proved. |
| APEX-BLK-9 | Blockade | 🟨 PARTIAL | NEW_FORMALIZATION | empirical spectral measures mu_n of A_{n,r}/sqrt n: all moments and all polynomial integrals converge to those of N(0,sigma_r^2); tightness. Missing: moment determinacy => weak convergence |
| APEX-QI-1 | Quantum | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | trace norm tr sqrt(A^H A): =sum/lambda/ for Hermitian A, zero iff A=0, unitary invariance, density matrices have norm 1, Helstrom variational form, triangle inequality (Hermitian), orthogonal pure states at distance 2. Not: triangle/Holder for non-Hermitian A |
| APEX-QI-2 | Quantum | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | Kraus channels: trace preserving, completely positive (Phi(x)id_k maps all PSD to PSD for every finite k), closed under composition and convex combination; unitary channels. Not: Choi/Stinespring converse |
| APEX-QI-3 | Quantum | 🟨 PARTIAL | NEW_FORMALIZATION | orthogonal-unitary noise with erasure flag: exact //(E-V0)(x)id (Phi+)//_1 = 2(1-(1-l)p0) and lower bound on diamondDist (density inputs, ancilla d). Missing: matching upper bound (needs trace-norm contractivity) and identification with standard diamond norm |
| APEX-COL-3 | Collatz | 🟩 KERNEL_PROVED | KNOWN_RESULT | Terras affine lemma for shortcut map; sound stopping-time certificates by residue mod 2^k; kernel counts of uncertified classes k=1..12 and 7495 classes mod 2^18 (density 2.86%), all others n>=2^18 have sigma(n)<=36. NOT a proof of Collatz; no cycle results |

## Сводка по 27 направлениям

IN_PROGRESS: 1, KERNEL_PROVED: 11, NOT_STARTED: 1, NUMERICAL_EVIDENCE: 2, OPEN: 7, PARTIAL: 5

## Карта зависимостей (доказано / открыто)

Узлы — модули и задачи; зелёные — доказано ядром, жёлтые — частично, серые — открыто.

```mermaid
graph LR
 TR[PXP.Trajectories/Walks]:::ok --> RAT[PXP.Rational: D^{m+1}]:::ok --> DEG[PXP.Degree: deg=3m-2]:::ok
 MDP[PXP.MaskDP]:::ok --> M8[8-й, 10-й моменты]:::ok
 DEG --> LC[Старший коэфф. W m,m,1]:::num
 GT[Blockade.General.Transfer]:::ok --> GR[General.Rational]:::ok --> GRS[General.Residue]:::ok --> CG[ConjGeneral ∀m,r]:::ok
 GRS --> GD[General.Degree: Lc m, знак]:::ok --> CG
 CG --> AS[Asymptotics: моменты ~ 2m-1 !! σ^2m]:::ok --> GA[Gaussian: моменты, полиномы, плотность]:::ok --> WL[Слабая сходимость к N 0,σ²]:::wip
 CG --> RED[Точный несократимый знаменатель]:::open
 TN[Quantum.TraceNorm]:::ok --> CP[Quantum.CPTP]:::ok --> ON[OrthogonalNoise: Φ⁺, нижняя оценка ◇]:::part
 CP --> CT[Сжимаемость, верхняя оценка ◇]:::wip --> ON
 B2[Anyon.Braid2D]:::ok --> FIB[Fibonacci: пентагон/гексагон]:::wip
 BC[Collatz.BoundedCorrection]:::ok --> ST[Collatz.StoppingTime: mod 2^18]:::ok --> CYC[Циклы / гипотеза Коллатца]:::open
 SH[S3.Harmonic]:::ok --> SS[S3.Sphere: спектр -n n+2 /R²]:::ok --> L2[L²-полнота, Ходж, Дирак]:::open
 SS --> YM[Янг–Миллс: масштаб; массовая щель]:::open
 AP[AKLT.Physical]:::ok --> AL[AKLT.Leakage]:::ok
 PR[Spectral.PositiveRepresentation]:::ok --> QG[Квантовая гравитация]:::open
 MC[Spectral.MixtureCumulants]:::ok --> COSM[Космология: тёмный сектор]:::part
 FE[Analysis.ForcedEnergy]:::ok --> NS[NS ℝ³ регулярность]:::open
 classDef ok fill:#2e7d32,color:#fff
 classDef part fill:#f9a825,color:#000
 classDef wip fill:#1565c0,color:#fff
 classDef num fill:#ef6c00,color:#fff
 classDef open fill:#9e9e9e,color:#000
```

