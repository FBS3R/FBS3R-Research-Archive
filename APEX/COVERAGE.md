# COVERAGE — покрытие обязательств APEX (раунд 5)

Сгенерировано `Audit/mk_coverage.py`. Реестр: **434** Lean-целей (`Audit/ACCEPTED_THEOREMS.txt`), все проверены ядром Lean 4.36 / Mathlib v4.36, аксиомы только `propext`, `Classical.choice`, `Quot.sound`.

Легенда: 🟩 KERNEL_PROVED · 🟨 PARTIAL · 🟦 IN_PROGRESS · 🟧 NUMERICAL_EVIDENCE · ⬜ OPEN / NOT_STARTED.
Статус «KERNEL_PROVED» означает доказанность сформулированного в Lean утверждения, а не решение открытой задачи.

| № | Обязательство | Направления (MISSION_STATE) | Результаты | Lean-целей |
|---|---|---|---|---|
| 1 | PXP: 10-й момент, старший коэффициент, асимптотика, гауссов предел | 🟩 2. PXP рациональная иерархия (deg=3m−2, вычет, знак) — KERNEL_PROVED<br>🟩 3. PXP 8-й момент (доказанный DP) — KERNEL_PROVED<br>🟨 4. PXP старший коэффициент W(m,m,1) — PARTIAL<br>🟩 5. PXP/блокада: асимптотика и гауссов предел — KERNEL_PROVED | PXP-1, PXP-2, PXP-3, PXP-5, PXP-6, PXP-7 | 10 |
| 2 | ConjGeneral для всех m, r | 🟩 6. Блокада r: размерности — KERNEL_PROVED<br>🟩 7. Блокада r: моменты, D_r^{m+1}, степень, конгруэнция — KERNEL_PROVED | BLK-1, BLK-2, BLK-2b, BLK-3, BLK-4, BLK-5, BLK-6, BLK-7, BLK-8, BLK-9, BLK-10 | 42 |
| 3 | Универсальные автоматы R[x]/(x²), закон переноса | 🟨 9. Общий закон переноса для автоматов (R[x]/(x²)) — PARTIAL | TRN-1 | 12 |
| 4 | AKLT: полнота, ранг 6 / ядро 18, интерпретации | 🟩 10. AKLT 625: физическая карта утечки — KERNEL_PROVED | AKLT-1, AKLT-2, AKLT-3 | 11 |
| 5 | Квантовая информация, каналы, diamond; FibonacciAnyon | 🟩 13. FibonacciAnyon: braid-классификация 2×2, норма дефекта — KERNEL_PROVED<br>🟩 14. FibonacciAnyon: пентагон, гексагон, универсальность — KERNEL_PROVED<br>🟩 15. Квантовые каналы, алмазная норма (BINDU VECTRA) — KERNEL_PROVED | ANY-1, QI-1, QI-2, QI-3, QI-4, ANY-2 | 45 |
| 6 | S³: гармоники, спектр, геометрия | 🟩 18. S³: гармонические многочлены, Фишер, dim (n+1)² — KERNEL_PROVED<br>🟨 19. S³: риманова геометрия, Ходж, Дирак — PARTIAL | S3-1, S3-2, S3-3 | 36 |
| 7 | Навье–Стокс | 🟩 16. Навье–Стокс: энергетическая оценка с силой (конечномерная) — KERNEL_PROVED<br>⬜ 17. Навье–Стокс: регулярность в ℝ³ — OPEN | NS-1, NS-2 | 11 |
| 8 | Янг–Миллс: масштаб, массовая щель | 🟨 21. Янга–Миллса: масштабирование λ(R)=R⁻²λ(1), массовая щель — PARTIAL | YM-1 | 28 |
| 9 | Квантовая гравитация, спектральное препятствие | 🟩 20. Спектральное препятствие exp(−ax)/x — KERNEL_PROVED<br>🟨 22. Квантовая гравитация (Fractal Foliation, CMC, связи, унитарность) — PARTIAL | SPC-1, SPC-4 | 19 |
| 10 | Космология: кумулянты, ядро оболочек | 🟨 23. Топология Вселенной, идентифицируемость (S³, RP³, S³/Γ) — PARTIAL<br>🟨 24. Космологическая постоянная Λ=3π/(ℓ_P² q), выбор q — PARTIAL<br>🟨 25. Тёмный сектор, кумулянты смесей — PARTIAL | SPC-2, COS-1, SPC-3, COS-2 | 50 |
| 11 | Коллатц: stopping time, циклы | 🟩 11. Коллатц: no-go ограниченной поправки (log и высота Цекендорфа) — KERNEL_PROVED<br>🟨 12. Коллатц: stopping-time сертификаты, циклы, 2-адика — PARTIAL | COL-1, COL-2, COL-3, COL-4 | 19 |
| 12 | Каталог открытых задач | ⬜ 27. Каталог открытых задач (Риман, P vs NP, Ходж, BSD, MLC, Гольдбах, близнецы, совершенные, Эрдёш, Рамсей) — OPEN | — | 0 |
| 13 | Единый закон | 🟨 26. Причинность, свет, единый закон — PARTIAL | UNI-1 | 31 |
| 14 | Аудит 101 работы архива, A1–A7 (Audit/ARCHIVE_AUDIT.md) | 🟨 1. Аудит/CI/сертификация — PARTIAL | — | 0 |

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
| APEX-BLK-9 | Blockade | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | empirical spectral measures mu_n of A_{n,r}/sqrt n converge WEAKLY to N(0,sigma_r^2), sigma_r^2=2rho_r^{r+1}/K_r: for every bounded continuous g, int g dmu_n -> int g phi (weak_limit); also characteristic functions, all moments, polynomial integrals, tightness. Limit stated with explicit density phi (not Mathlib gaussianReal) |
| APEX-QI-1 | Quantum | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | trace norm tr sqrt(A^H A): =sum/lambda/ for Hermitian A, zero iff A=0, invariance under unitary conjugation U A U*, density matrices have norm 1, Helstrom variational form, triangle inequality (Hermitian), orthogonal pure states at distance 2. Not: triangle/Holder for non-Hermitian A |
| APEX-QI-2 | Quantum | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | Kraus channels: trace preserving, completely positive (Phi(x)id_k maps all PSD to PSD for every finite k), closed under composition and convex combination; unitary channels. Not: Choi/Stinespring converse |
| APEX-QI-3 | Quantum | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | orthogonal-unitary noise with erasure flag: diamondDist(E,V0) = 2(1-(1-l)p0) EXACTLY (upper bound for every density input; lower bound attained at Phi+). diamondDist = sup over density inputs with ancilla dim d; identification with the standard diamond norm (Watrous 3.46/3.51) not formalised. Upper bound does not use HS-orthogonality (only the lower bound does) |
| APEX-COL-3 | Collatz | 🟩 KERNEL_PROVED | KNOWN_RESULT | Terras affine lemma for shortcut map; sound stopping-time certificates by residue mod 2^k; kernel counts of uncertified classes k=1..12 and 7495 classes mod 2^18 (density 2.86%), all others n>=2^18 have sigma(n)<=36. NOT a proof of Collatz; no cycle results |
| APEX-QI-4 | Quantum | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | trace-norm contractivity of Kraus channels on Hermitian inputs (via Kraus dual and Helstrom form), data processing //Phi A - Phi B//_1 <= //A-B//_1, post-processing monotonicity of diamondDist. Not: non-Hermitian inputs, pre-composition |
| APEX-ANY-2 | Anyon | 🟩 KERNEL_PROVED | KNOWN_RESULT | Fibonacci anyons (tau x tau = 1 + tau): F-matrix [[phi^-1, phi^-1/2],[phi^-1/2,-phi^-1]] orthogonal, F^2=1; pentagon for all 512 label choices; both hexagons over C (R^tt_1=e^{-4pi i/5}, R^tt_t=e^{3pi i/5}, Bonderson convention up to R^{ab}_c = R^{ba}_c, which holds for Fibonacci) for all 64 label choices; braid relation for sigma1, sigma2=F sigma1 F; order exactly 10 up to phase. Proof: exact arithmetic in Z[zeta]/Phi_10[s] by decide +kernel, transferred to C. Not: gauge classification, fusion-category structure |
| APEX-TRN-1 | Transfer | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | MISSION-03 algebraic core: finite Neumann formula; event ring R[x_1..x_k]/(x_i^2) with degree filtration, products of >k/2 degree>=2 elements vanish; transfer law (I-z(T0+U))^{-1} = sum_{j<=floor(k/2)} R0 (zUR0)^j in Mat_d(E[[z]]) for any T0 and degree>=2 U; universal denominator det(I-zT0)^{floor(k/2)+1} (polynomial adjugate form); degree-0 part reproduces the spatial automaton. Not: top-coefficient extraction, exactness of the dominant pole (cancellation possible), concrete PXP instance |
| APEX-BLK-10 | Blockade | 🟩 KERNEL_PROVED | COROLLARY_OF_BLK-6 | immediate corollary of the residue congruence (BLK-6), since D_r(0)=1: for all m,r>=1 the numerator P of ConjGeneral is coprime to D_r over Q, so P/D_r^{m+1} is in lowest terms over Q[X] (no cancellation, incl. r = 4 mod 6 where X^2-X+1 / D_r, iff proved); kernel values Lc(1..5) = 2,-4,36,-568,14560 |
| APEX-COL-4 | Collatz | 🟩 KERNEL_PROVED | KNOWN_RESULT | every 1 <= n <= 2^20 reaches 1 (kernel, 64 chunks); any nontrivial cycle has all elements > 2^20 and its minimum lies in one of 7495 residue classes mod 2^18. NOT a proof of Collatz or of non-existence of cycles (literature: verified to ~2^71) |
| APEX-NS-2 | Analysis | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | energy bounds for x(t)=x(0)+int v, v = -nu A x - Q x + F a.e., F only L^1, A,Q arbitrary maps on a Hilbert space with <Qy,y>=0, <Ay,y> >= lam/y/^2: //x T// <= e^{-kT}//x0// + int e^{-k(T-s)}//F//; no finite-time blow-up of local solutions (classical with F continuous on [0,T), or integral-form with F in L^1). NOT Navier-Stokes regularity; no existence/uniqueness |
| APEX-S3-3 | S3 | 🟩 KERNEL_PROVED | KNOWN_RESULT | S^3 geometry: unit quaternions (own structure Q, Hamilton product) form a group acting by isometries of R^4; group isomorphism unit quaternions = SU(2) with det = normSq; Hopf map h(z,w)=(2z w-bar, /z/^2-/w/^2) maps S^3 onto S^2, fibres are exactly U(1)-orbits, pairwise disjoint great circles (S^3 cap real 2-plane); polar decomposition x = r u unique. Not: linking number, Mathlib Quaternion (not built), quaternionic q i q-bar formula |
| APEX-SPC-3 | Spectral | 🟩 KERNEL_PROVED | KNOWN_RESULT | full moment-cumulant hierarchy: recursion, uniqueness, formal relation egf(m) = exp(egf(kappa)) over char-0 fields, additivity under binomial convolution, scaling kappa_n(cX)=c^n kappa_n; Prony: Hankel = V^T D V, det H_p = prod w * prod (x_j-x_i)^2, recurrence, unique Prony coefficients, identifiability of finite mixtures (nodes and weights up to permutation) from s_0..s_{2p-1}, rank H_m = p for m >= p, number of components determined |
| APEX-SPC-4 | QuantumGravity | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | strengthened spectral theorem for positive measures rho on [0,inf) with int (1+s)^-1 drho < inf (rho may be infinite): xG(x) nondecreasing, G antitone/positive, xG(x) -> rho([0,inf)) in [0,inf] (monotone convergence); no positive representation if xG(x)=o(1) or xf(x) decreases anywhere, in particular for exp(-ax)/x; sharp bound: uniform relative error of any positive spectral approximation of exp(-at)/t on [x,y] is >= tanh(a(y-x)/2), attained by a point mass at 0; Loewner-monotone matrix version for finitely-atomic PSD measures and per-polarisation bounds. Scope: Kallen-Lehmann-type necessary condition only; says nothing about existence of quantum gravity |
| APEX-YM-1 | YangMills | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | abstract spectral layer of the mass-gap problem: Laplace criterion TFAE (support in [m,inf) <=> C(t)<=C(0)e^{-mt} <=> subexponential decay at every m'<m); polynomial decay gives no gap (e^{-E}dE, C=1/(1+t)); finite-dim Hilbert version for e^{-tA} on vacuum complement; transfer-matrix bound and converse; physical-scale bound with lambda_2 <= e^{-a Delta}; gap preserved under limits with UNIFORM Delta; non-uniform gaps lost (delta_{1/k} -> delta_0; lambda_2 = e^{-a_k^2}). The YM mass gap itself is OPEN: the uniform bound lambda_2(T_a) <= e^{-a Delta} is only a hypothesis |
| APEX-COS-2 | Cosmology | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | Lambda underdetermination: FLRW Christoffel/Ricci computed from the metric (t-dependent metrics); de Sitter of every radius l satisfies the trace-free equations, Lambda_eff = 3/l^2 injective; with perfect fluid + continuity, R + 8 pi G T = 4 Lambda is an integration constant and every Lambda >= 0 is realised; vacuum shifts drop out. Selector no-go: coercive discrete-convex Gamma has minimisers (interval), strict convexity alone does not give uniqueness ((2q-1)^2), every q* is the unique minimiser of some strictly convex coercive Gamma; affine reweighting Z_q -> C e^{aq} Z_q (named in the 08-17 paper) moves the minimiser to any q*; the 08-12 edge selector minimiser q_edge = Xi exp(16 pi^2/(b g^2)) takes any value > Xi. Archive inputs: 292 = round(n(q_obs)) from observed H0, Omega_Lambda (Python), 1+pi/50 fitted to residual. Does not refute global/microscopic selection; no claim about observed Lambda |
| APEX-UNI-1 | Unified | 🟩 KERNEL_PROVED | NEW_FORMALIZATION | scale-consistency layer R o U_l(t) = U_l'(t) o R: exact consistency for all t iff generators intertwine (Banach operators and real matrices with exp); discrete defect recursion and bound, linear growth k//D// for contractions, sharp (shift/position example); composition of coarse-grainings and subadditive defects; intertwiners map eigenvectors/fixed points; no-go: consistency does not determine the state space (trivial dynamics, stochastic total mass, non-isomorphic consistent models Fin 3 -> Fin 2); Kemeny-Snell lumpability <=> exact consistency of block aggregation. Derives no physical law and no GR/QFT/LCDM-distinguishing prediction |

## Сводка по 27 направлениям

KERNEL_PROVED: 13, NUMERICAL_EVIDENCE: 1, OPEN: 2, PARTIAL: 11

## Карта зависимостей (доказано / открыто)

Узлы — модули и задачи; зелёные — доказано ядром, жёлтые — частично, серые — открыто.

```mermaid
graph LR
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
 SS --> YM[Янг–Миллс: массовая щель]:::open
 YSG[YM.SpectralGap: критерии, сохранение при равномерной щели]:::ok --> YM
 EXT[Внешние: OpenAI-YM без щели, 4Y-M условно]:::part --> YM
 AP[AKLT.Physical]:::ok --> AL[AKLT.Leakage]:::ok
 PR[Spectral.PositiveRepresentation]:::ok --> STR[Spectral.Strengthened: tanh, матрицы]:::ok --> QG[Квантовая гравитация]:::open
 MC[Spectral.MixtureCumulants]:::ok --> PRO[Spectral.Prony: кумулянты, идентифицируемость]:::ok --> COSM[Космология: тёмный сектор]:::part
 FE[Analysis.ForcedEnergy]:::ok --> IE[IntegralEnergy: L¹, без взрыва]:::ok --> NS[NS ℝ³ регулярность]:::open
 NIL[Transfer.Nilpotent: закон переноса, знаменатель]:::ok --> AUT[Несокращение полюса, PXP-конкретизация]:::open
 LU[Cosmology.LambdaUnderdetermination: Λ не фиксируется, no-go селектора]:::ok --> LAM[Λ из микродинамики]:::open
 UC[Unified.Consistency: R∘U=U′∘R, дефекты, no-go]:::ok --> UL[Единый закон, предсказания]:::open
 classDef ok fill:#2e7d32,color:#fff
 classDef part fill:#f9a825,color:#000
 classDef wip fill:#1565c0,color:#fff
 classDef num fill:#ef6c00,color:#fff
 classDef open fill:#9e9e9e,color:#000
```

