# Реестр результатов (честный счёт)

Каждый результат — теорема, проверенная ядром Lean 4 (без `sorry`, только стандартные
аксиомы), либо машинно проверенный контрпример. Тривиальные вспомогательные леммы
(`weight_s2`, `helicity_sign`, `single_slope_injective`, `de_sitter_capacity`,
`golden_scaling` — последняя уже есть в Mathlib) **в счёт не входят**.

**Итог: 56 результатов = 6 найденных ошибок (раздел A) + 50 машинных верификаций (раздел B).**
Покрытие по каждой из 101 папки репозитория — в `COVERAGE.md`.
Ни один результат не решает открытую проблему (Коллатц, Навье–Стокс, Янг–Миллс, MLC).

## A. Найденные ошибки и исправления (6)

| # | Препринт | Утверждение статьи | Что доказано в Lean | Имя в Lean |
|---|---|---|---|---|
| A1 | Zeckendorf–φ Collatz (2025-09-28) | «не top-third ⇒ рост высоты ≤ 2» | ложно при n = 11 (рост 3) | `Collatz.refined_odd_step_counterexample` |
| A2 | Bell / S³ topology (2026-04-15), Yang–Mills (2026-04-19) | единственность фибоначчиевой стратификации | гипотезы несовместны; `F₂+F₅=6` не Фибоначчи | `FibStrat.no_additively_closed_partition_with_ratio_gt_one`, `fib_not_additively_closed` |
| A3 | Bell / S³ topology (2026-04-15) | `Φ⁺` даёт `E = −cos θ` | `⟨σx⊗σx⟩_{Φ⁺} = +1`; верно только для `Ψ⁻` | `Bell.bell_Phi_plus`, `singlet_Psi_minus` |
| A4 | Yang–Mills на S³ (2026-04-19) | порог `3/R²` | `3/R²` нет ни в спектре `curl²`, ни в спектре Стокса архива | `KillingBeltrami.no_three_in_curl_or_stokes_spectrum` |
| A5 | Mandelbrot MLC (2025-03-05) | «подмножество связного диска связно» | контрпример `{0,1} ⊆ [0,1]` | `Misc.subset_of_connected_not_connected` |
| A6 | Hierarchical Bethe (2026-04-21) | Бине `F_n = (φ^{n+2}−ψ^{n+2})/√5` при `F₁=3` | формула даёт 2 при n=1; верно `φ^{n+3}`, `F_n = Fib(n+3)` | `Checks.paper_binet_wrong`, `F_binet` |

## B. Машинно проверенные утверждения архива (50)

| # | Препринт | Результат | Имя в Lean |
|---|---|---|---|
| B1 | Collatz | чётный шаг `h(n/2)+1 ≤ h(n)` | `Collatz.even_step` |
| B2 | Collatz | нечётный шаг `h(3n+1) ≤ h(n)+3` | `Collatz.odd_step` |
| B3 | Collatz | дрейф суперполушага `h(T n)−h(n) ≤ 3−m` | `Collatz.superstep_drift_int` |
| B4 | Collatz | no-go: наивная `V=h−2ν₂`, грубый сертификат | `naive_lyapunov_fails`, `no_coarse_certificate` |
| B5 | Killing–Beltrami (2026-09) | теорема о дефекте представления (абстрактно) | `KillingBeltrami.defect` |
| B6 | Killing–Beltrami | коэффициенты `−2k/(k+2)²`, `2(k+4)/(k+2)²` ≠ 0 | `defect_coeffs`, `defect_coeffs_ne_zero` |
| B7 | Killing–Beltrami | `D = ad + 2/(k+2)(ad₋−ad₊)` | `D_minus_ad` |
| B8 | Killing–Beltrami | коэффициент поляризации и хиральные значения | `KB_coefficient`, `chiral_values` |
| B9 | Killing–Beltrami | `dim E_{k,σ} = (k+1)(k+3)` | `shell_dim` |
| B10 | Killing–Beltrami | Казимир `Δ_iso = 2curl²` | `casimir_eq_two_curl_sq` |
| B11 | Killing–Beltrami | собственное значение Стокса `k(k+4)/R²` | `stokes_eigenvalue` |
| B12 | Killing–Beltrami | явные структурные коэффициенты | `structure_coefficients` |
| B13 | Killing–Beltrami | прецессия не совершает работы (энергетический баланс) | `Precession.energy_balance` |
| B14 | Killing–Beltrami | точное затухание `‖v(t)‖ = e^{−ct}‖v₀‖` | `Precession.exact_decay` |
| B15 | Killing–Beltrami | поляризованное векторное тождество | `Lamb.polarized` |
| B16 | Killing–Beltrami | тождество Лэмба для дифференцируемых полей | `Lamb.lamb` |
| B17 | Killing–Beltrami | Бельтрами ⇒ адвекция — градиент | `Lamb.beltrami_advection_is_gradient` |
| B18 | (плоский аналог) | ABC: `curl U = U`, `div U = 0` | `ABC.curl_eq`, `ABC.div_eq_zero` |
| B19 | (плоский аналог) | ABC — точное стационарное решение Эйлера | `ABC.steady_euler` |
| B20 | Killing–Beltrami | `Σ 2(k+1)(k+3)/(k+2)^s = 2(ζ(s−2)−ζ(s))` | `ZetaShell.shell_sum` (+ `Z_eq_riemannZeta`) |
| B21 | Killing–Beltrami | точный полюс `lim (s−3)C_s = 1/(3π²)` | `ZetaShell.residue_C` |
| B22 | Killing–Beltrami | условная оценка энтропии `S ≥ δ log(M/C)` | `Entropy.conditional_entropy_bound` |
| B23 | Killing–Beltrami | постоянное ядро равно `N/V` | `Projector.kernel_const` |
| B24 | Killing–Beltrami | точная оценка концентрации `‖w‖²/w(x)² ≥ V/N` | `Projector.concentration`, `pointwise_sharp` |
| B25 | Bell–Hopf PRA (2026-04-30) | CHSH ≤ 2 для любой ЛСП-модели | `Bell.chsh` |
| B26 | Bell–Hopf PRA | граница Цирельсона `2√2` для синглетного ядра | `Bell.tsirelson_singlet` |
| B27 | Bell–Hopf PRA | `S = −2√2` при настройках статьи; ни одна ЛСП-модель не воспроизводит ядро | `chsh_value_PRA`, `no_LHV_reproduces_singlet` |
| B28 | Bell–Hopf PRA | жёсткость заряда Черна `q = ±1` | `Bell.chern_rigidity` |
| B29 | Bell–Hopf, Suspension (2026-07) | отображение Хопфа `S³→S²`, инвариантность слоёв U(1) | `hopf_S3_to_S2`, `hopf_fibre` |
| B30 | Yang–Mills (2026-04-19) | разбиение `ℤ≥1` интервалами Фибоначчи | `FibStrat.fib_partition` |
| B31 | Causal–Spectral (2026-07-07) | объём геодезического шара `2πR³(s/R − ½sin(2s/R))` и `2π²R³` | `CausalSpectral.ball_volume`, `total_volume` |
| B32 | Causal–Spectral | `Γ' = (2/π)sin²τ`, `Γ(τ)+Γ(π−τ)=1`, `Γ(π/2)=½` | `hasDerivAt_Γ`, `Γ_symm`, `Γ_half` |
| B33 | Causal–Spectral | скалярная ёмкость: отсечка и `M(M+1)(2M+1)/6` | `scalar_cutoff`, `scalar_count` |
| B34 | Causal–Spectral | TT-ёмкость `M(M−1)(2M+11)/3` | `TT_count` |
| B35 | Causal–Spectral | дираковская ёмкость `2(M+1)(M+2)(M+3)/3` | `dirac_count` |
| B36 | Hierarchical Bethe | нулевые моды: `dim ker ≥ F_{n−1} − 1` | `Checks.zero_mode_multiplicity` |
| B37 | Ricci-type flow (2026-07-02) | кривизны Бергера: `R`, `|Ric|²`, `|Rm|²`, предел `64/a⁴` | `scalar_curv`, `ric_sq`, `rm_sq`, `rm_sq_fibre_collapse` |
| B38 | Ricci-type flow | уравнение отношения `u̇ = 8u(1−u)/x` | `Checks.ratio_ode` |
| B39 | GHZ balancing (2026-05-02) | факторизация `V = q·2r/(1+r²) = q/cosh(ln r)` | `Checks.design_factorization` |
| B40 | GHZ balancing | `V ≤ q`, равенство ⇔ `r = 1` | `Checks.balance_penalty` |
| B41 | Dilation algebra (2026-08-10), Trace-free (2026-08-12) | `p = −ε − (A/3)ε'`; `A^n` — собственные функции `A d/dA`; корни `P_val`; плотность валюации; ядро вакуумного сдвига `P_tr(T−ρ₀g) = P_tr(T)` | `work_identity`, `dilation_eigen`, `P_val_roots`, `valuation_density`, `vacuum_kernel` |
| B42 | Fibonacci anyon braid (2026-11-09) | `F² = 1` и точное соотношение кос `B₁B₂B₁ = B₂B₁B₂` при `u = φ⁻¹`, `v = √u`, `R = diag(e^{−4πi/5}, e^{3πi/5})` | `FibonacciAnyon.fibonacci_braid`, `F_sq` |
| B43 | Fibonacci anyon braid (новое) | замкнутая форма дефекта `RFRFR − FRFRFRF = (a−b)Q(a,b)·[[1,−v],[−v,−1]]`, критерий: соотношение кос ⇔ `a = b ∨ Q(a,b) = 0`, `Q = (2u−1)a² + (2−3u)ab + (2u−1)b²` | `FibonacciAnyon.braid_defect`, `braid_iff` |
| B44 | Rational Spectral Hierarchies (2026-10-23) | адрес Цекендорфа `r(s) = Σ sⱼF_{n−j+2}` — биекция `𝒞ₙ → {0,…,F_{n+2}−1}`; `|𝒞ₙ| = F_{n+2}`; флип меняет адрес на `F_{n−j+2}` | `Zeckendorf.image_rk`, `rk_injOn`, `card_C`, `flip_changes_address`, `mem_C_iff` |
| B45 | Planck boundary (2026-05-05) | `ζ(−3) = 1/120`, постоянная Казимира конформного скаляра на S³ `C_ζ = ½ζ(−3) = 1/240`, плотность `ρ = C_ζ/(2π²a⁴) = 1/(480π²a⁴)` | `Planck.riemannZeta_neg_three`, `casimir_constant`, `casimir_density_scalar` |
| B46 | Planck boundary | `Ḣ = ä/a − H²`; две формы скаляра Кречмана совпадают; при `|H| ≤ h`, `|Ḣ| ≤ g`, `a ≥ ℓ_P`: `K ≤ 12[(g+h²)² + (h²+1/ℓ_P²)²]` (явная константа в `K ≤ C/ℓ_P⁴`) | `Planck.hasDerivAt_hubble`, `kretschmann_forms`, `kretschmann_bound` |
| B47 | Curvature barriers (2026-07-05) | производная по конформному масштабу `d/ds e^{3s}Φ(e^{−4s}K) = 3Φ − 4KΦ'`; для `Φ = K^q` знак правильный ⇔ `q > 3/4` | `Barriers.scale_derivative`, `power_threshold` |
| B48 | Curvature barriers | для стены Планка `Φ = (K+δ)^q/(K_P−K)^p`: `4KΦ' − 3Φ = Φ(4qK/(K+δ) + 4pK/(K_P−K) − 3)` | `Barriers.hasDerivAt_Φb`, `barrier_sign` |
| B49 | Curvature barriers (**уточнение**) | из `|Rm|² = 4|Ric|² − R² ≤ K₀` следует `Ric ≥ −√(K₀/2)`; константа `1/√2` точна и лучше заявленной `1/2 + 1/√3` (утверждение статьи верно, но не точно) | `Barriers.ricci_lower_bound_sharp`, `ricci_bound_attained`, `paper_constant_weaker` |
| B50 | Finite spectral closure NS (2026-09-20) | для `ẋ + νAx + Q(x,x) = F` с `⟪Ax,x⟫ ≥ 0`, `⟪Q(x,x),x⟫ = 0` и непрерывной `F`: `‖x(t)‖² + 1 ≤ (‖x₀‖²+1)·exp(∫₀ᵗ‖F‖)` — в точном конечном редуцирующем пространстве взрыва нет | `FiniteReduction.energy_bound`, `no_blowup` |

### Численная проверка (Python, не Lean)
Trace-free gravity (2026-08-12): `q₀ = πφ⁵⁸⁴/(1+π/50) = 3.3072514607139791698…×10¹²²`
воспроизводится; `Λ = 3π/(ℓ_P² q₀) ≈ 1.09×10⁻⁵² м⁻²`. Это проверка арифметики, а не вывод
значения Λ: выбор `N_φ = 292` и множителя `1+π/50` статья вводит сама.

Rational Spectral Hierarchies (2026-10-23): производящие функции `Σ Tr A_n^{2m} zⁿ` при `2m = 4, 6, 8`
совпадают с прямым вычислением следов для `n ≤ 10` (`scripts/pxp_moments_check.py`). Это проверка, а не
доказательство теоремы о знаменателе `(1−z−z²)^{m+1}`.
