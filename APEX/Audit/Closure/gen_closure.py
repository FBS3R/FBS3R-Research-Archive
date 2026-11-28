#!/usr/bin/env python3
"""Generate CLOSURE_PLAN.json/.md, REFUTED_PROPAGATION.json and corrections/*.md.
Read-only on /home/claude/repo. Outputs to /tmp/claude-0/archive2/."""
import json, os, collections

REPO = "/home/claude/repo"
OUT = "/tmp/claude-0/archive2"
AUD = json.load(open(f"{REPO}/APEX/Audit/ARCHIVE_AUDIT.json"))
APEX = {r["id"]: r for r in json.load(open(f"{REPO}/APEX/Audit/APEX_RESULTS.json"))}
WORK = {w["id"]: w for w in AUD}

# ---------------------------------------------------------------- open claims
# key: (work, claim index) -> plan fields
P = {}
def e(w, i, stmt, cls, step, lean=None, deps=(), fdeps=(), prio=2, sub=None, status=None, note=None):
    P[(f"FBS3R-{w}", i)] = dict(statement_en=stmt, cls=cls, next_step=step, lean_target=lean,
        apex_deps=list(deps), fbs3r_deps=list(fdeps), priority=prio, a_subtarget=sub,
        proposed_status=status, note=note)

# W004 Poincare / fractal
e("W004",1,"The 'fractal time' + modified Ricci flow derivation in the paper is a rigorous proof of the Poincare conjecture.",
  "D","Meta-claim about a proof, not a theorem. Reformulate as the list of concrete lemmas the derivation uses (definition of the flow, short-time existence, singularity analysis); each lemma is then B. Poincare itself is KNOWN (Perelman).",
  None,[],[],3,status="UNSUPPORTED (proof not checkable as written)")
e("W004",2,"The fractal structure of the gauge field yields a spectral and mass gap for Yang-Mills.",
  "C","Clay Millennium problem. Only the abstract spectral layer exists (APEX-YM-1: gap survives a limit only under a uniform bound). No step to take before a constructive 4D YM theory exists.",
  None,["APEX-YM-1"],[],3)
e("W004",3,"The 'fractal' Ricci flow dg/dt = -2Ric + Q with a quantum term Q removes singularities without surgery.",
  "D","Q is never defined, so the claim has no content yet. Reformulate with an explicit Q; then test it against the archive's own no-go for bounded forcing (W059) and the curvature-barrier thresholds (B47-B49).",
  None,[],["B47","B48","B49"],3)
# W005 MLC
e("W005",0,"The Mandelbrot set is locally connected (MLC).",
  "C","Open research problem (Yoccoz/Lyubich partial results). The paper's argument is withdrawn: its key step is refuted (A5) and its second step is false (claim #2).",
  None,[],["A5"],3,status="OPEN (paper's proof: UNSUPPORTED_AFTER_REFUTATION)")
e("W005",2,"If local regions are simply connected (pi_1 = 0), then the space is locally connected.",
  "A","Prove the counterexample: a star-convex (so contractible, so simply connected) planar set that is not locally connected, the 'harmonic fan' (union of segments from 0 to (1,1/n) and to (1,0)). Mathlib has StarConvex.contractibleSpace and SimplyConnectedSpace.ofContractible.",
  "theorem APEX.Topology.simplyConnected_not_locallyConnected : ∃ S : Set (ℝ × ℝ), StarConvex ℝ 0 S ∧ SimplyConnectedSpace S ∧ ¬ LocallyConnectedSpace S",
  [],["A5"],1,status="DISPROVED once the Lean target compiles (currently OPEN, elementary error)")
# W014 nonlocal gravity
e("W014",3,"Thm IV.3 (All-loop finiteness): every loop integral of the nonlocal e^{-s Box} gravity theory converges.",
  "B","Needs a Feynman-graph and power-counting library (Weinberg's theorem), which Mathlib does not have. Before that, search for a counterexample: vertices carry e^{+s p^2} growth, so check a 2-loop graph in Euclidean signature where vertex growth beats propagator damping. Claim #4 already shows the one-loop example diverges in the IR.",
  None,["APEX-SPC-4"],[],3,status="UNSUPPORTED (counterexample search recommended)")
e("W014",4,"Prop. IV.1 example: int d^4p e^{-2sp^2}/(p^2)^2 converges thanks to Gaussian suppression.",
  "A","False as stated: in 4D the integrand behaves like r^3 dr / r^4 near 0, so the integral diverges logarithmically in the IR. Formalize the divergence through the radial reduction (MeasureTheory.integral_fun_norm_addHaar or polar lintegral) together with the non-integrability of 1/r on (0,1).",
  "theorem APEX.Gravity.oneLoop_ir_divergent (s : ℝ) : ¬ MeasureTheory.IntegrableOn (fun p : EuclideanSpace ℝ (Fin 4) => Real.exp (-2*s*‖p‖^2) / ‖p‖^4) (Metric.ball 0 1)",
  [],[],1,status="DISPROVED once the Lean target compiles (currently OPEN, elementary error)")
e("W014",7,"Section VI: the theory is a UV-complete, ghost-free (unitary) theory of gravity.",
  "D","'UV-complete theory' has no definition here. The checkable form is 'the spin-2 propagator e^{-sx}/x has a positive Kallen-Lehmann representation'. APEX-SPC-4 (no_representation_exp_div) already refutes exactly that form, so the standard route to unitarity is closed. Mark the reformulated statement DISPROVED and the original UNSUPPORTED.",
  None,["APEX-SPC-4","APEX-SPC-1"],[],2,status="UNSUPPORTED (reformulated version refuted by APEX-SPC-4)")
# W024 Collatz
e("W024",4,"Collatz global convergence follows from either sufficient reduction A' or B' (conditional implication).",
  "A","The implication is formalizable, but its B' half relies on inequality (2) and on Prop. 2 (refuted, A1). Re-prove B' with the correct integrand (3 - nu2), which is Prop. 1/B3, as the paper's own Remark 2 already does. Note also that APEX-COL-1 (no_bounded_height_correction) makes the conclusion of Theorem 4 (A') unsatisfiable when it is required for all odd n > 1, so A' is an empty reduction. The unconditional Collatz conjecture is C.",
  "theorem APEX.Collatz.cumulative_halvings_le (o : ℕ → ℕ) (ho : ∀ j, o (j+1) = syracuse (o j)) (hodd : ∀ j, Odd (o j)) (J : ℕ) : (∑ j in Finset.range J, (padicValNat 2 (3 * o j + 1) : ℤ)) ≤ 3 * J + fibHeight (o 0)  -- corrected core of Thm 1/Thm 5; plus APEX.Collatz.reductionA_vacuous from no_bounded_height_correction",
  ["APEX-COL-1","APEX-COL-2","APEX-COL-3","APEX-COL-4"],["A1","B1","B2","B3"],2,
  status="UNSUPPORTED_AFTER_REFUTATION (B' part); A' vacuous by APEX-COL-1",
  sub="Corrected B' (integrand 3 - nu2) and the vacuity of A' are class A; the Collatz conjecture itself is C.")
# W034
e("W034",6,"Thm 6.1: the Wheeler-DeWitt solution on S^3 does not factorize over spacelike-separated regions.",
  "D","The Wheeler-DeWitt solution space is not defined. The paper's proof actually uses unique continuation of Laplace eigenfunctions. Reformulate as: 'a finite sum of degree-n spherical harmonics on S^3 that vanishes on a nonempty open subset of S^3 is identically zero'. That version is A (polynomials restricted to a sphere; APEX-S3-1/S3-2).",
  "theorem APEX.S3.harmonic_eq_zero_of_vanish_on_open {h : MvPolynomial (Fin 4) ℝ} (hh : h ∈ HH ℝ n) {U : Set E4} (hU : IsOpen U) (hne : (U ∩ sphere).Nonempty) (hv : ∀ y ∈ U ∩ sphere, eval y h = 0) : h = 0",
  ["APEX-S3-1","APEX-S3-2"],[],2,sub="The unique-continuation reformulation is class A.")
# W036 YM
e("W036",4,"Yang-Mills mass gap in the infinite-volume limit (stated as a conjecture).",
  "C","Clay Millennium problem. APEX-YM-1: a gap survives the limit only under a uniform lower bound (gap_of_limit), and non-uniform gaps are lost (nonuniform_gap_lost).",
  None,["APEX-YM-1"],[],3)
e("W036",5,"Abstract: the finite-volume threshold 'is a lower bound' for the full non-perturbative infinite-volume gap.",
  "D","As stated it is vacuous or false. The threshold sqrt(3)/R tends to 0 (APEX-S3-2 tendsto_sphEigen), the value 3/R^2 itself is refuted (A4), and non-uniform gaps are lost (APEX-YM-1). Reformulate: 'inf_R Delta(R) > 0 uniformly' (open, C). The archive's own later works W066 and W068 (Prop. 13.1/27.1, KERNEL_PROVED) already state the correct no-go.",
  None,["APEX-YM-1","APEX-S3-2"],["A4"],2,status="UNSUPPORTED_AFTER_REFUTATION")
# W038 Bethe
e("W038",2,"Thm 2/3: Schur-complement recursion of the characteristic polynomial chi_{n+1}(l) = l^{F_{n-1}-1}[l chi_n(l) - F_{n-1} q_n(l)] (maximally coupled B_n = 1 1^T); resolvent equation; norm bounds.",
  "A","Matrix.det_fromBlocks_zero₂₂ / det_fromBlocks₁₁ (Schur) plus the matrix determinant lemma (Matrix.det_add_col_mul_row) give Thm 2/3 directly. The norm bounds need the paper's exact statement. This claim does not depend on the refuted Binet formula: it only uses the block sizes F_n and F_{n-1}.",
  "theorem APEX.Bethe.charpoly_recursion (A : Matrix (Fin p) (Fin p) ℚ) (q : ℕ) (hq : 1 ≤ q) (λ : ℚ) : (λ • 1 - Matrix.fromBlocks A (allOnes p q) (allOnes q p) 0).det = λ^(q-1) * (λ * (λ • 1 - A).det - q * (dotProduct 1 ((λ • 1 - A).adjugate.mulVec 1)))",
  [],["B36"],1)
# W046
e("W046",2,"The Planck epoch is a regular self-adjoint boundary of minisuperspace a in [l_P, inf); norm conservation.",
  "B","Needs unbounded self-adjoint operators, deficiency indices and boundary conditions for Sturm-Liouville operators on a half-line. Mathlib has only bounded operators. The minisuperspace Hamiltonian must also be specified.",
  None,[],["B45","B46"],3)
# W047
e("W047",3,"Prop. 12: for d >= 3 no single scalar visibility exists: pair magnitudes |K_ij| and diagonals K_ii do not determine the branch kernel up to diagonal-unitary gauge (cycle phases remain).",
  "A","Explicit 3x3 family K(Phi) = eta Q(Phi). The gauge-invariant cycle product K_01 K_12 K_20 = eta^3 q^3 e^{i Phi} distinguishes Phi, while all moduli coincide.",
  "theorem APEX.Transfer.no_scalar_visibility_d3 : ∃ K K' : Matrix (Fin 3) (Fin 3) ℂ, K.IsHermitian ∧ K'.IsHermitian ∧ (∀ i j, ‖K i j‖ = ‖K' i j‖) ∧ ¬ ∃ d : Fin 3 → ℂ, (∀ i, ‖d i‖ = 1) ∧ ∀ i j, K' i j = d i * K i j * star (d j)",
  ["APEX-TRN-1"],["B65"],1)
# W050-055 residual cosmology
e("W050",2,"Theorem 'no topology-only amplitude'; local quantum no-go for global topology.",
  "D","Bundle of informal no-go statements. Split it, define 'topology-only amplitude' as a map from (S^3/Gamma data) to amplitudes, then reassess. Likely B (quotients S^3/Gamma, spectral multiplicities).",
  None,["APEX-COS-1"],[],3)
e("W051",3,"Reduction of the tensor residual to the locally-FLRW class; amplitude selection by a flux lattice.",
  "D","Not a single statement. Needs Lorentzian tensor calculus (B) for the first part and a definition of the 'flux lattice' selector for the second, to compare with the APEX-COS-2 selector no-go.",
  None,["APEX-COS-2"],["B58","B59"],3)
e("W053",1,"Theorem 4 (IRTC): on S^3/Gamma with Gamma-equivariant lifts, linear perturbation evolution is the cover evolution restricted to P_Gamma V_beta; the quotient changes only initial data, multiplicities and sky projection.",
  "B","Needs Riemannian coverings/quotients by free isometric actions and linear PDE on manifolds. The finite-dimensional shadow (an equivariant linear map commutes with the projector onto invariants) is A and could be stated first.",
  None,[],[],3,sub="Finite-dim equivariance lemma: if T commutes with the group action, T preserves the invariant subspace (Mathlib-level).")
e("W054",2,"Transfer/quotient-projection separation, quotient-sky covariance, residual-transfer separability.",
  "D","Bundle; restatement of W053 Thm 4 plus definitions. Split it and reuse the W053 plan.",None,[],[],3)
e("W055",2,"Topological decoupling of amplitudes; completeness of the standard; registry of closure routes.",
  "D","'Completeness of a standard' and the 'registry' are not mathematical statements. Only 'topological decoupling' can be reformulated, as in W050.",None,["APEX-COS-1","APEX-COS-2"],[],3)
# W058/059/064 Ricci-type flows
e("W058",0,"Bounded tensor filtering does not prevent singularities; a coercive term 2<C^h(Rm),Rm> <= -gamma|Rm|^3 + ... is needed.",
  "B","The full PDE statement needs Ricci-flow theory on manifolds (B). Within the paper's homogeneous Hopf/Berger ODE sector it reduces to an ODE comparison (same target as W059#2).",
  None,["APEX-NS-2"],["B37","B38","B47","B48"],3,sub="Berger-sector ODE version: see W059#2.")
e("W058",2,"Fibre-only forcing mu sigma3 (x) sigma3 changes sign at u = (c/a)^2 = 12/11: dK_B/dtau|_fib = mu * 8(11u-12)/x^3.",
  "A","Differentiate the Berger |Rm|^2 formula (B37 rm_sq) along x' = 0, z' = mu and factor the result. First check that B37's K_B matches the paper's eq. (35).",
  "theorem APEX.Ricci.fibre_forcing_sign (x z μ : ℝ) (hx : 0 < x) (hz : 0 < z) : HasDerivAt (fun t => K_B x (z + μ*t)) (μ * 8 * (11*(z/x) - 12) / x^3) 0 ∧ (0 < μ → (μ * 8 * (11*(z/x) - 12) / x^3 < 0 ↔ z/x < 12/11))",
  [],["B37","B38"],1)
e("W059",2,"No-go for bounded, traceless and Lambda-forcing in the Hopf-lifted (Berger) flow; invariant region for the Planck barrier.",
  "A","Within the homogeneous Berger ODE system (B37/B38): (i) for bounded forcing, a blow-up comparison for K_B; (ii) the traceless forcing vanishes at u = 1; (iii) Lambda-forcing gives dK/dtau = -4 Lambda K, i.e. order |Rm|^2; (iv) an invariant region {K <= K_P} by a barrier/sign argument (B48 barrier_sign).",
  "theorem APEX.Ricci.planck_barrier_invariant (sol : ℝ → ℝ × ℝ) (hsol : ∀ t, HasDerivAt sol (bergerField F (sol t)) t) (h0 : K_B (sol 0) < K_P) (hbar : barrier condition of B48) : ∀ t ≥ 0, K_B (sol t) < K_P",
  ["APEX-NS-2"],["B37","B38","B47","B48"],2)
e("W061",3,"Conjecture 5.6: effective non-recurrence of an open hierarchy.",
  "D","The paper itself says (Remark 5.7) this is not a theorem until the Hamiltonian, state space, measure and transitions are specified. Not provable as stated.",None,[],[],3)
e("W064",3,"Berger no-go for additive K-potentials; failure as a PDE mechanism (heat-kernel argument).",
  "B","The PDE heat-kernel part needs analysis on manifolds. The Berger-sector derivative sign is A, using B47/B48 (scale_derivative, power_threshold).",
  None,[],["B47","B48","B49"],3,sub="Berger-sector no-go: sign of 3Phi - 4KPhi' (A).")
# W075/076 dilation algebra
e("W075",2,"Complete invariants, Fisher-length rigidity, Koopman-Hankel spectral fingerprint for finite dilation profiles (Thms VI.1-VI.9).",
  "A","All of these are finite-dimensional algebra on positive exponential mixtures. Hankel-pencil fingerprint = Prony (APEX-SPC-3). Bhatia-Davis and Hankel PSD are already proved (B51-B53). Formalize Thm VI.1 (pencil) and VI.8 (Koopman-Hankel) first, then the Fisher sum rules VI.9.",
  "theorem APEX.Valuation.hankel_pencil_fingerprint (w : Fin p → ℝ) (s : Fin p → ℝ) (hw : ∀ i, 0 < w i) (hs : Function.Injective s) : eigenvalues of the pencil (H₁, H₀) of moments m_n = ∑ w_i (e^{s_i})^n are exactly {e^{s_i}}",
  ["APEX-SPC-3","APEX-SPC-2"],["B41","B51","B52","B53"],2)
e("W076",2,"Thm VI.6: R^2 acts freely on positive coefficient vectors by (a,b).c_i = e^{a+b s_i} c_i, quotient of dimension k-2; Thm VI.10: universal logistic/tanh two-branch normal form.",
  "A","In log coordinates the action is translation by span{1, s}, which is 2-dimensional for k >= 2 with distinct s_i, so the action is free and finrank of the quotient is k-2. Thm VI.10 is an elementary identity: p+(x) = 1/(1+e^{-Delta(x-x_x)}), kappa1 = s_bar + (Delta/2) tanh(Delta(x-x_x)/2).",
  "theorem APEX.Valuation.two_branch_normal_form (c₋ c₊ s₋ s₊ x : ℝ) (hc : 0 < c₋ ∧ 0 < c₊) (hs : s₋ < s₊) : let Δ := s₊ - s₋; let xx := Real.log (c₋/c₊) / Δ; c₊*exp(s₊*x)/(c₋*exp(s₋*x)+c₊*exp(s₊*x)) = 1/(1+exp(-Δ*(x-xx))) ∧ (s₋*c₋*exp(s₋*x)+s₊*c₊*exp(s₊*x))/(c₋*exp(s₋*x)+c₊*exp(s₊*x)) = (s₋+s₊)/2 + Δ/2 * tanh(Δ*(x-xx)/2)   -- plus APEX.Valuation.finrank_quotient_eq (k-2)",
  ["APEX-SPC-3"],["B41","B51"],1)
e("W077",2,"Boundary Hamiltonian, spin-c Dirac operator, eta-invariant, 'Chern-Simons capacity lock', Planck-Bradlow selector.",
  "B","Needs APS index theory and eta-invariants (absent from Mathlib), plus definitions of the 'capacity lock' and the selector. The selector part should be checked against the APEX-COS-2 selector no-go.",
  None,["APEX-COS-2"],[],3)
e("W078",4,"Thm LIV.1: Xi_edge = 0.99916928 and b g^2 = 0.5597545859987624455 computed in the APS/HC/Kronecker scheme, hence q_edge = Xi exp(16 pi^2/(b g^2)) = q0.",
  "E","Numerical and tautological. b g^2 is defined as 16 pi^2/ln(q0/Xi), so q_edge = q0 holds by construction, and Xi_edge is input, not computed. Certificate: an interval-arithmetic script that reproduces b g^2 from (q0, Xi), plus a statement that the 'agreement' is an identity. APEX-COS-2 qEdge_any_target shows q_edge can take any value > Xi.",
  None,["APEX-COS-2"],[],2,status="NUMERICAL_EVIDENCE at most (tautological); recommend UNSUPPORTED as a derivation")
e("W078",7,"No-go XXIII.1: a selector built from finitely many O(1) coefficients and powers of q, ln q, without an exponential hierarchy, has no natural isolated minimum at q ~ 10^122.",
  "D","'Natural' is undefined. Reformulate with explicit coefficient bounds |c_i| <= C and degree bounds, as a statement about where minimisers of such Gamma can lie. The APEX-COS-2 selector results (selector_nogo, poisson_selector_any_target) are the relevant layer: without such bounds every q* is attainable.",
  None,["APEX-COS-2"],[],2)
e("W080",1,"Molecular quotient space, compound-Poisson rigidity, dichotomy of invariant subalgebras, Jones index.",
  "B","The Jones index needs a von Neumann subfactor library (absent). Compound-Poisson rigidity is probability (Mathlib-level once stated). Split the claim first.",
  None,["APEX-SPC-2","APEX-SPC-3"],[],3)
# W081-082 relational dynamics
e("W081",0,"Prop. 3: for phi_a'' + alpha_a L(W) phi_a = 0, every nonzero eigenmode has omega_1^2/omega_2^2 = alpha_1/alpha_2; changing W at fixed distinct alpha_a cannot equalize speeds.",
  "A","Immediate eigenvector computation: L z = nu z with nu != 0 gives omega_a^2 = alpha_a nu.",
  "theorem APEX.Relational.speed_ratio_indep (L : Matrix n n ℝ) (z : n → ℝ) (ν α₁ α₂ : ℝ) (hz : L.mulVec z = ν • z) (hν : ν ≠ 0) (ha : 0 < α₁ ∧ 0 < α₂) : (α₁ * ν) / (α₂ * ν) = α₁ / α₂ ∧ (α₁ ≠ α₂ → α₁ * ν ≠ α₂ * ν)",
  [],[],1)
e("W081",1,"Thm 4: all r massless branches share one characteristic cone iff the kinetic matrix D00 = v^2 I_r for some v^2 > 0.",
  "A","Spectral theorem for real symmetric matrices (Matrix.IsHermitian.spectral_theorem). det(-w^2 I + t D) = prod(-w^2 + t d_j), so the cones coincide iff all d_j are equal iff D = v^2 I.",
  "theorem APEX.Relational.common_cone_iff (D : Matrix (Fin r) (Fin r) ℝ) (hD : D.PosDef) : (∀ t > 0, ∀ ω : ℝ, (-(ω^2) • 1 + t • D).det = 0 ↔ ∀ j, ω^2 = t * eig D j) ↔ ∃ v2 > 0, D = v2 • 1   -- or equivalently: Set.range (eig D) is a singleton ↔ D = v2 • 1",
  [],[],1)
e("W082",0,"Spectral conditions for a common low-energy cone; response limits on chains.",
  "D","Bundle. The cone condition is covered by W081#1 (A). 'Response limits' must be stated precisely before they can be assessed.",None,[],[],3)
# W083 field reconstruction
e("W083",0,"Null space of q spherical maps has dimension N_{L-q}, N_j = (j+1)(j+2)(2j+3)/6.",
  "A","In the sector-block model (one COS-1 shell-observation block of degree d = L - l for each (l,m), l <= L) combine finrank_ker_shellObs with Rank.rank_count/N_closed. Identifying that block model with harmonic analysis on S^3 (Gegenbauer radial factors) is B and must be stated as an explicit hypothesis.",
  "theorem APEX.Cosmology.finrank_ker_sphericalMaps (L q : ℕ) (hq : q ≤ L + 1) (χ : Fin q → ℝ) (hχ : χ injective, in (0,π)) : Module.finrank ℝ (LinearMap.ker (blockObs L q χ)) = N (L - q)",
  ["APEX-COS-1","APEX-S3-1","APEX-S3-2"],["B69"],1,sub="Block-model statement is A; the S^3 harmonic identification is B.")
e("W083",1,"Thin-shell spectrum; conditional two-shell curvature reconstruction.",
  "B","Needs radial (Gegenbauer) eigenfunctions on S^3 and their nodal structure. After APEX-S3-2 the step is to formalize the radial factors r_{nl}(chi) as explicit polynomials in cos chi times sin^l chi.",
  None,["APEX-COS-1","APEX-S3-2"],[],2)
e("W083",2,"Thm 6: exact local statistical degeneracy: P(chi) = M(chi)^{-1} M(chi0) P(0) > 0 near chi0 leaves the Gaussian sky unchanged; profiled Fisher information for chi is zero.",
  "A","Specialize APEX.Cosmology.nonident_local to the upper-triangular M with diagonal a_ll^2 sin^{2l} chi > 0 on (0, pi), so det != 0 and M^{-1} is continuous. Then add the linear-algebra lemma: if the chi-score lies in the span of the nuisance scores, the profiled Fisher information (a Schur complement) is 0.",
  "theorem APEX.Cosmology.profiled_fisher_zero (I : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hI : I = Jᵀ * W * J) (hspan : J.col 0 ∈ Submodule.span ℝ (Set.range fun i : Fin k => J.col i.succ)) : schurComplement I 0 = 0   -- with nonident_local applied to the triangular M",
  ["APEX-COS-1"],[],1)
# W084-086 NS on S^3
e("W084",0,"Finite-reduction criterion: A W ⊆ W and Q(W,W) ⊆ W iff ‖D_W‖_HS = 0, with D_W = ((I-Pi_W)A e_i, (I-Pi_W)Q(e_i,e_j)) over an orthonormal basis of W.",
  "A","Finite-dimensional inner-product-space lemma. orthogonalProjection plus Orthonormal basis expansion; ‖·‖_HS = 0 iff every component is 0.",
  "theorem APEX.NS.finite_reduction_iff (A : E →ₗ[ℝ] E) (Q : E →ₗ[ℝ] E →ₗ[ℝ] E) (W : Submodule ℝ E) (b : OrthonormalBasis ι ℝ W) : ((∀ w ∈ W, A w ∈ W) ∧ ∀ x ∈ W, ∀ y ∈ W, Q x y ∈ W) ↔ (∑ i, ‖(W.orthogonalProjectionᗮ) (A (b i))‖^2 + ∑ i, ∑ j, ‖(Wᗮ.orthogonalProjection) (Q (b i) (b j))‖^2 = 0)",
  ["APEX-NS-1","APEX-NS-2"],["B50"],1)
e("W084",2,"Relative singular branch of forced Navier-Stokes on S^3_R under five external hypotheses.",
  "C","Linked to the Clay NS regularity problem. The conditional implication could be formalized only after the five hypotheses are stated as Lean predicates. Low priority.",
  None,["APEX-NS-2"],["B50"],3)
e("W085",0,"Projected quadratic convection vanishes on every signed curl shell; Grassmannian of exact reductions.",
  "B","Needs the Leray projection on S^3 (Hodge decomposition of vector fields). The flat analogue is B17 (beltrami_advection_is_gradient). In the algebraic shell model of FBS3R.KillingBeltrami, Q(u,u) in gradients for u in one shell is A.",
  None,[],["B5","B12","B15","B16","B17"],2,sub="Shell-model identity Q(u,u) = 0 after projection (A).")
e("W085",3,"Thm V.3: Parseval Killing-response frame sum_{tau,a} R_{a tau}^* R_{a tau} = I_H; two orthonormal same-chirality probes determine the field; conditioning bounds.",
  "A","Finite-dimensional frame identity in the Killing-Beltrami shell model (so(4) = su(2)_L + su(2)_R acting on E_{k,sigma}). Uses the structure coefficients B12 and the Casimir B10. Conditioning bounds follow from the frame identity.",
  "theorem APEX.KB.parseval_killing_frame (k : ℕ) (σ : Sign) : ∑ τ, ∑ a : Fin 3, (R a τ)† ∘L (R a τ) = ContinuousLinearMap.id ℝ (Shell k σ)",
  ["APEX-S3-3"],["B5","B7","B10","B12"],2)
e("W086",3,"Rigidity: every finite exact reduction containing the Killing algebra is a union of complete signed shells; toric classification.",
  "B","Needs representation theory of SO(4) on vector fields on S^3 (Peter-Weyl or explicit shell decomposition). The B5 defect theorem is the algebraic core.",
  None,["APEX-S3-3"],["B5","B6","B7","B9"],3)
# W087/089/090 null Beltrami / Maxwell
e("W087",0,"For homogeneous holomorphic p(z1,z2) of degree m, F0 = pX satisfies curl F0 = (m+2)F0, div F0 = 0, F0.F0 = 0, hence an exact Maxwell solution.",
  "A","In the left-invariant-frame model (fields written as polynomial combinations of X1, X2, X3, with derivations on C[z1,z2,z1bar,z2bar] restricted to S^3), check the three identities by computation. The claim is A only in that model; identifying the model with Riemannian curl on S^3 is the S^3 library item 19 (PARTIAL).",
  "theorem APEX.S3.holomorphic_beltrami (p : MvPolynomial (Fin 2) ℂ) (hp : p.IsHomogeneous m) : curlFrame (p • Xplus) = (m+2 : ℂ) • (p • Xplus) ∧ divFrame (p • Xplus) = 0 ∧ dotFrame (p • Xplus) (p • Xplus) = 0",
  ["APEX-S3-1","APEX-S3-3"],["B9","B10"],2)
e("W087",1,"Converse within the ansatz fX; the chiral subspace of dimension (m+1) inside the (m+1)(m+3)-dimensional curl eigenspace.",
  "B","The converse needs analysis of smooth f on S^3 (not only polynomials). The dimension count (m+1) of degree-m binary forms is trivial, and (m+1)(m+3) is B9.",
  None,["APEX-S3-1"],["B9"],3,sub="Dimension count (A).")
e("W087",2,"Conformal transport to Minkowski, Bateman form, Penrose representation of degree -4.",
  "B","Twistor theory and the Penrose transform are not in Mathlib.",None,[],[],3)
e("W089",0,"Global classification of null curl eigenfields on round S^3 (up to isometry: p(z1,z2)(X2+iX3)).",
  "B","Global PDE classification on S^3: needs the Hodge/curl spectral theory of S^3 and analytic arguments.",None,["APEX-S3-3"],["B9"],3)
e("W089",1,"Dynamics of Bateman knotted links; exact sextic cohomological bridge to nonlinear gravitons.",
  "B","Twistor cohomology (absent). The 'bridge' must be stated precisely first.",None,[],[],3)
e("W090",0,"Classification of smooth non-vanishing null curl eigenfields with positive eigenvalue m+2.",
  "B","Same as W089#0.",None,["APEX-S3-3"],["B9"],3)
e("W090",1,"Structural obstructions: Poincare-Casimir, causal incompleteness of ambitwistor data.",
  "D","Informal obstructions. They need precise definitions before they can be assessed.",None,[],[],3)
# W091
e("W091",0,"Multi-speed Jacobi and Hopf-Killing exact solutions of viscous flow on S^3; energy, helicity and Noether identities.",
  "B","Needs NS on S^3 (vector calculus on manifolds). The exact-decay layer is B13/B14; the Hopf-Killing algebra is FBS3R.KillingBeltrami.",
  None,["APEX-NS-2"],["B13","B14","B16"],3)
e("W091",2,"Prop. 14.3: topology cannot be recovered from integrated time traces alone (p = z1^m and q = sqrt(m) z1^{m-1} z2 have equal integrated intensity but different root divisors).",
  "B","Needs integration on S^3 (the moment identity (107): int |sum c_k z1^{m-k} z2^k|^2 = Vol/(m+1) sum |c_k|^2/C(m,k)). Given (107) as a hypothesis, the rest is A: both sums equal 1, and the root multiplicities (m) and (m-1,1) differ.",
  None,["APEX-S3-3","APEX-UNI-1"],[],2,sub="Conditional on (107): equality of intensities and non-equivalence of divisors (A).")
# W092 Hopf triad
e("W092",0,"An orthogonal triad of Hopf maps gives a homogeneous isotropic stress-energy tensor (quadratic sector ∝ a^-2, quartic ∝ a^-4).",
  "B","Needs the sigma-model stress tensor on S^3. In the left-invariant frame the pointwise identities |dn_a|^2 = 24, |F_a|^2 = 48 are algebraic (A-subtarget).",
  None,["APEX-S3-3"],[],3,sub="Frame identities sum |dn_a|^2 = 24, |F_a|^2 = 48 (A).")
e("W092",1,"Prop. 1: for 0 < eta < 1 and 0 < 4h^2 D < C^2, a(t)^2 = (C + sqrt(C^2-4h^2 D) cosh(2h(t-t0)))/(2h^2) is a regular, time-symmetric bounce solving a'^2 = h^2a^2 - C + D/a^2, a'' = h^2 a - D/a^3.",
  "A","Explicit ODE verification with x = a^2: x'^2 = 4(h^2x^2 - Cx + D). HasDerivAt computations plus a positivity lemma (x >= x_+ > 0). The converse (a nondegenerate upper-root bounce requires (9)) is the discriminant condition.",
  "theorem APEX.Cosmology.hopf_triad_bounce (h C D t₀ : ℝ) (hh : 0 < h) (hD : 0 < D) (hdisc : 4*h^2*D < C^2) (hC : 0 < C) : let a := fun t => Real.sqrt ((C + Real.sqrt (C^2 - 4*h^2*D) * Real.cosh (2*h*(t-t₀)))/(2*h^2)); (∀ t, 0 < a t) ∧ (∀ t, (deriv a t)^2 = h^2*(a t)^2 - C + D/(a t)^2) ∧ (∀ t, deriv (deriv a) t = h^2 * a t - D/(a t)^3) ∧ (∀ t, a (2*t₀ - t) = a t)",
  ["APEX-COS-2"],["B46"],1)
# W093 meta-causal
e("W093",0,"Minimax error for a periodic peak reduces to a fractional problem on the divisor hypergraph; exact 'ladders' for 3 and 4 prime divisors.",
  "E","Finite LP. The certificate is primal and dual rational solutions checked by exact arithmetic (script under APEX/Certificates). It can then be lifted to Lean by `decide`/`norm_num` on the rational certificate.",
  None,[],[],3)
e("W093",1,"Sections on Berger spectra, Hopf phase reduction and the homogeneous Ricci-flow integral.",
  "D","Bundle of sections, not one claim. Split it. The Berger curvature parts overlap B37/B38.",None,[],["B37","B38"],3)
e("W093",2,"Thm 6 (predictive rank 2 with exact classical two-state countermodel), Thm 8 (four-time obstruction to two classical hidden states), Thm 9 (five-time Hankel certificate: -det H3(f) = rho^2 sin^2 theta (1+rho^2-2rho cos theta)^2/8 > 0, rank 3).",
  "A","Closed-form finite identities. Thm 6: c_t = (1+lambda^t)/2 = (M_lambda^t)_{11} and det = (1-lambda)^2/4. Thm 9: compute the 3x3 Hankel determinant symbolically. A two-state linear model has Hankel rank <= 2, so det H3 = 0, by APEX-SPC-3 (det_hankel_eq_zero_of_lt / rank_hankel).",
  "theorem APEX.Memory.five_time_hankel (ρ θ : ℝ) (hρ : 0 < ρ ∧ ρ ≤ 1) (hθ : 0 < θ ∧ θ < π) : let f := fun k : ℕ => (1 - ρ^k * Real.cos (k*θ))/2; -(Matrix.of fun i j : Fin 3 => f (i+j)).det = ρ^2 * Real.sin θ^2 / 8 * (1 + ρ^2 - 2*ρ*Real.cos θ)^2 ∧ 0 < -(Matrix.of fun i j : Fin 3 => f (i+j)).det   -- plus rank_two_countermodel (Thm 6) and two_state_hankel_det_zero (via SPC-3)",
  ["APEX-SPC-3"],["B51"],1)
# W094/095/096
e("W094",0,"Ground states are non-nested cycles; rescaled metric-measure spaces converge to a circle.",
  "B","Gromov-Hausdorff (or measured GH) convergence is not in Mathlib in usable form. The combinatorial ground-state part may be A once the energy functional is stated.",None,[],[],3)
e("W094",2,"Metastability and convergence to a common one-dimensional causal propagator.",
  "D","Informal; 'convergence' and 'metastability' are not specified.",None,[],[],3)
e("W095",0,"Spectral constraints, response limits, universal null calibration; quantitative reconstruction-locality interface.",
  "D","Bundle; overlaps W081/W082. Split it and reuse W081#1.",None,[],[],3)
e("W096",2,"Homotopy-class (Hopf invariant) certificate for PL maps S^3 -> S^2 via linking of preimages; measurement budgets.",
  "B","Needs the Hopf invariant, linking numbers and PL topology. APEX-S3-3 explicitly excludes linking number.",None,["APEX-S3-3"],[],3)
e("W097",3,"Exact weighted fourth-moment certificate in O(n) under diagonal disorder (Thm 2.1, Zeckendorf-indexed phase response).",
  "A","Finite combinatorial identity for Tr (A_n + D)^4 on the Fibonacci cube. Extend the proved mask-DP (APEX-PXP-6) with diagonal weights; the Zeckendorf address bijection is B44.",
  "theorem APEX.PXP.weighted_fourth_moment_certificate (n : ℕ) (d : FibCube n → ℝ) : Matrix.trace ((A n + Matrix.diagonal d)^4) = linearCertificate n d   -- certificate as defined in Thm 2.1, computed by an O(n) recursion",
  ["APEX-PXP-6","APEX-PXP-1"],["B44"],2)
e("W098",2,"Prop. 1: detuning/calibration budget: ‖[U(T)-U0(T)]P‖ <= int_0^T e(t)dt =: eps_T, ‖QU(T)P‖^2 <= eps_T^2, ‖U_T - U_{0,T}‖_⋄ <= 2 eps_T.",
  "A","Time-independent (or piecewise-constant) case first: ‖e^{-iT(H0+E)} - e^{-iTH0}‖ <= T‖E‖ through the Duhamel integral (Mathlib NormedSpace.exp + HasDerivAt). Then use APEX-QI-1..4 to get diamondDist(U,U0) <= 2‖U-U0‖. The time-dependent version needs propagators of linear ODEs (Mathlib-level through Gronwall, but longer).",
  "theorem APEX.Quantum.detuning_budget_const (H₀ E : Matrix n n ℂ) (hH : H₀.IsHermitian) (hE : E.IsHermitian) (T : ℝ) (hT : 0 ≤ T) : ‖exp (-(I*T) • (H₀+E)) - exp (-(I*T) • H₀)‖ ≤ T * ‖E‖ ∧ diamondDist (unitaryChannel (exp (-(I*T) • (H₀+E)))) (unitaryChannel (exp (-(I*T) • H₀))) ≤ 2 * T * ‖E‖",
  ["APEX-QI-1","APEX-QI-2","APEX-QI-3","APEX-QI-4"],[],2)
e("W100",3,"Thm 7.1: telescoping bound d(E_n∘...∘E_1, U_n∘...∘U_1) <= sum_j d(E_j, U_j) for CPTP maps.",
  "A","APEX-QI-4 gives post-composition monotonicity. Still missing: pre-composition monotonicity d(E∘Phi, U∘Phi) <= d(E,U), which holds because Phi ⊗ id maps density matrices to density matrices (APEX-QI-2 completelyPositive plus trace preservation), and the triangle inequality for diamondDist (APEX-QI-1 traceNorm_sum_le, Hermitian case). Then induct on n.",
  "theorem APEX.Quantum.diamondDist_telescope (E U : Fin n → KrausChannel d) : diamondDist (compList E) (compList U) ≤ ∑ j, diamondDist (E j) (U j)   -- via APEX.Quantum.diamondDist_precomp_le and diamondDist_triangle",
  ["APEX-QI-1","APEX-QI-2","APEX-QI-3","APEX-QI-4"],[],1)

# ---------------------------------------------------------------- refuted claims
REF = [
 dict(claim="FBS3R-W005#1", a="A5", work="FBS3R-W005",
   quote="Therefore, the intersection U – as a subset of this region – is also connected and contains c0.",
   refutation="A subset of a connected set need not be connected. Kernel-checked counterexample {0,1} ⊆ [0,1]: FBS3R.Misc.subset_of_connected_not_connected : ∃ S T : Set ℝ, IsConnected T ∧ S ⊆ T ∧ S.Nonempty ∧ ¬ IsPreconnected S.",
   lean=["FBS3R.Misc.subset_of_connected_not_connected"],
   corrected="U = {V < x_N} ∩ B(c0,ε) is an open subset of ℂ containing c0. Its connected component containing c0 is a connected open neighbourhood of c0 in ℂ, because open subsets of ℂ are locally connected. This says nothing about connectedness of M ∩ U, which is what local connectivity of the Mandelbrot set M requires. No correct version of the step yields MLC.",
   corrected_apex=None, corrected_lean_status="standard topology (Mathlib: isOpen_connectedComponentIn / locallyConnectedSpace); no APEX id",
   deps=[("FBS3R-W005#0","OPEN","OPEN (problem); paper's proof UNSUPPORTED_AFTER_REFUTATION","MLC conclusion of the paper rests on this step."),
         ("FBS3R-W005#2","OPEN","DISPROVED_PENDING_LEAN (independently false; see CLOSURE_PLAN W005#2)","Second route (pi_1 = 0 => local connectivity) is itself false (harmonic fan / comb).")],
   nondeps=["Other works mentioning 'Mandelbrot' (W007, W014, W017, W020, W049, W070, W088) only cite Mandelbrot's 1982 book, use it as an image or list MLC as open; none relies on W005."]),
 dict(claim="FBS3R-W024#2", a="A1", work="FBS3R-W024",
   quote="Proposition 2 (Refined odd-step). If n is top-third then h(3n+1) − h(n) ≤ 3; otherwise the increase is ≤ 2.",
   refutation="n = 11: x = log_φ(√5·11) ∈ [6, 6+2/3), so 11 is not top-third, yet h(34) = h(11) + 3. Lean: FBS3R.Collatz.refined_odd_step_counterexample.",
   lean=["FBS3R.Collatz.refined_odd_step_counterexample"],
   corrected="For every n ≥ 1: h(n) + 2 ≤ h(3n+1) ≤ h(n) + 3 (APEX.Collatz.fibHeight_three_mul_add_one). In each Fibonacci layer [F_k, F_{k+1}) (k ≥ 2), exactly ⌊(F_{k+1} − F_k + 1)/3⌋ integers have gain 3 (APEX.Collatz.card_gain_three). Gain 3 is not confined to top-third n. The superstep drift is h(T n) − h(n) ≤ 3 − ν₂(3n+1) (B3).",
   corrected_apex="APEX-COL-2", corrected_lean_status="KERNEL_PROVED (APEX-COL-2; FBS3R B2, B3)",
   deps=[("FBS3R-W024#4","OPEN","UNSUPPORTED_AFTER_REFUTATION (B' part)","Inequality (2) k_{J+1} − k_J ≤ (2 + I_J) − A_J, Thm 1 (conditional descent) and Thm 5 (B', integrand 2 + I − ν₂) use Prop. 2. The corrected versions use 3 − ν₂ (the paper's Remark 2). Reduction A' (Thm 4) does not use Prop. 2, but its conclusion is unsatisfiable for all odd n > 1 by APEX-COL-1 no_bounded_height_correction."),
         ("FBS3R-W024 Thm 1 (conditional descent; not a separate audit claim)","(part of #4)","UNSUPPORTED_AFTER_REFUTATION; corrected: hypothesis liminf A_J ≥ 3 + ε","Uses (2)."),
         ("FBS3R-W024 Thm 3 (no uniform negativity)","(not listed)","unaffected","δ₁ witness works with either integrand.")],
   nondeps=["'Collatz' and 'top-third' occur only in W024; no other work depends on it."]),
 dict(claim="FBS3R-W034#0", a="A2", work="FBS3R-W034",
   quote="Theorem 4.5 (Uniqueness of the Fibonacci Stratification). Among all non-overlapping … convergent ratio a_{n+1}/a_n → r > 1, the Fibonacci partition (with r = φ) is the unique minimally redundant gapless self-similar indexing.",
   refutation="The hypotheses are inconsistent. No strictly increasing a : ℕ → ℕ with a 0 = 1 that is closed under addition has a_{n+1}/a_n → r > 1 (FBS3R.FibStrat.no_additively_closed_partition_with_ratio_gt_one). The Fibonacci numbers themselves are not additively closed: F₂ + F₅ = 6 (FBS3R.FibStrat.fib_not_additively_closed).",
   lean=["FBS3R.FibStrat.no_additively_closed_partition_with_ratio_gt_one","FBS3R.FibStrat.fib_not_additively_closed"],
   corrected="(i) The Fibonacci intervals [F_n, F_{n+1}), n ≥ 2, partition ℤ≥1: every m ≥ 1 lies in exactly one (FBS3R.FibStrat.fib_partition, B30). (ii) The class of additively closed, strictly increasing ℕ-sequences starting at 1 with ratio limit r > 1 is empty, so the uniqueness theorem is vacuous. No uniqueness statement for the Fibonacci partition is proved.",
   corrected_apex=None, corrected_lean_status="KERNEL_PROVED in FBS3R-Lean (B30 + A2); no APEX id",
   deps=[("FBS3R-W034#3","HEURISTIC/PHYSICAL_MODEL","UNSUPPORTED_AFTER_REFUTATION","Thm 4.8 (Bell nonlocality from hyperconnectivity) uses Def. 4.7, F_k = F_m + F_n for every pair, which is exactly the false additive closure (fib_not_additively_closed), and §4.6 invokes Thm 4.5."),
         ("FBS3R-W034#5","KERNEL_PROVED","unchanged","The partition (B30) is the true residue of A2.")],
   nondeps=["W030 (Noether identities) and W040 (quasi-local charges) appeal to the Zeckendorf–Lekkerkerker uniqueness theorem, which is true. They do not use Thm 4.5.","W046 Prop. II.4 uses only the band partition (B30).","W042 lists W034 only as bibliography item [9] and never cites it in the text."]),
 dict(claim="FBS3R-W034#1", a="A3", work="FBS3R-W034",
   quote="Consider a maximally entangled two-qubit state |Φ+⟩ = (|00⟩ + |11⟩)/√2. … E(a, b) = ⟨Φ+|(σ·a) ⊗ (σ·b)|Φ+⟩ = −cos θ_ab (Theorem 3.3).",
   refutation="For Φ⁺: ⟨σx⊗σx⟩ = +1, ⟨σy⊗σy⟩ = −1, ⟨σz⊗σz⟩ = +1 (FBS3R.Bell.bell_Phi_plus, stated for the unnormalised vector with values 2, −2, 2). So E(a,a) = +1 for a = x, not −1.",
   lean=["FBS3R.Bell.bell_Phi_plus","FBS3R.Bell.singlet_Psi_minus"],
   corrected="For the singlet |Ψ⁻⟩ = (|01⟩ − |10⟩)/√2: E(a,b) = −a·b = −cos θ_ab (axis values −1, −1, −1: FBS3R.Bell.singlet_Psi_minus; full kernel, CHSH −2√2 and Chern rigidity q = ±1 in W043: B26–B28). For Φ⁺: E(a,b) = a_x b_x − a_y b_y + a_z b_z.",
   corrected_apex=None, corrected_lean_status="KERNEL_PROVED in FBS3R-Lean (B25–B28, A3 singlet part); the general Φ⁺ bilinear form is classical and not formalized beyond the axis values",
   deps=[("FBS3R-W034#7","HEURISTIC/PHYSICAL_MODEL","UNSUPPORTED_AFTER_REFUTATION","Cor. 5.3 (Tsirelson excess ∝ c₁) is derived from Thm 3.3 with the Φ⁺ kernel (Conclusions item 2–3)."),
         ("FBS3R-W034#3","HEURISTIC/PHYSICAL_MODEL","UNSUPPORTED_AFTER_REFUTATION","Also uses §5.1 (Φ⁺)."),
         ("FBS3R-W034#4","KNOWN_RESULT","unchanged","Tsirelson is state-independent.")],
   nondeps=["W043 (PRA version) uses the singlet and is the corrected edition (KERNEL_PROVED B25–B29).","W058 cites only W043."]),
 dict(claim="FBS3R-W036#0", a="A4", work="FBS3R-W036",
   quote="Corollary II.2 (Threshold on S³). On S³(R) the lowest transverse vector Laplacian eigenvalue is λ^V_1 = 3/R², giving Δ(S³(R)) = √3/R. … yielding λ^V_ℓ = ℓ(ℓ+2)/R² for ℓ ≥ 1.",
   refutation="ℓ(ℓ+2)/R² is the SCALAR Laplace spectrum on S³(R). For divergence-free (transverse) vector fields the archive's own spectra are curl² = (k+2)²/R² and Stokes k(k+4)/R² (k ≥ 0). 3 occurs in neither, and min curl² = 4/R² (FBS3R.KillingBeltrami.no_three_in_curl_or_stokes_spectrum: (k+2)² ≠ 3 ∧ k(k+4) ≠ 3 ∧ 4 ≤ (k+2)²).",
   lean=["FBS3R.KillingBeltrami.no_three_in_curl_or_stokes_spectrum"],
   corrected="(i) In the spectra {(k+2)²/R²} (curl² = Hodge Laplacian on coexact 1-forms) and {k(k+4)/R²} (Stokes), 3/R² does not occur. The minimum of the first is 4/R², at k = 0 (Lean, A4). So the free linearised transverse-gluon threshold is Δ = 2/R, not √3/R (classical: Hodge spectrum of coexact 1-forms on S³ is (ℓ+1)²/R², ℓ ≥ 1; completeness is not formalized). (ii) 3/R² is the first nonzero eigenvalue of the SCALAR Laplacian. APEX-S3-2 proves that degree-n harmonic polynomials restrict to eigenfunctions with eigenvalue n(n+2)/R² (sphLapF_of_harmonic), so n = 1 gives 3/R². Completeness of that spectrum is not formalized. (iii) Any such threshold → 0 as R → ∞ (APEX-S3-2 tendsto_sphEigen), so it bounds no infinite-volume gap (APEX-YM-1 nonuniform_gap_lost).",
   corrected_apex="APEX-S3-2 (scalar part); APEX-YM-1 (limit no-go)", corrected_lean_status="vector part KERNEL_PROVED as stated in (i) (FBS3R A4); scalar eigenfunction part APEX-S3-2; spectral completeness not formalized",
   deps=[("FBS3R-W036#3","HEURISTIC/PHYSICAL_MODEL","UNSUPPORTED_AFTER_REFUTATION","Δ = √3 Λ_QCD ≈ 520 MeV and the glueball hierarchy use λ₁ = 3/R² (A4) and the Fibonacci uniqueness (A2). With the corrected threshold the same convention gives Δ = 2Λ_QCD, which is still heuristic."),
         ("FBS3R-W036#5","OPEN","UNSUPPORTED_AFTER_REFUTATION","The 'lower bound' claim is built on the refuted 3/R² and contradicts APEX-YM-1/S3-2."),
         ("FBS3R-W036#4","OPEN","OPEN (unchanged; Clay problem)","The conjecture does not depend on the value of the threshold.")],
   nondeps=["W066 Prop. 15.x and W068 Prop. 16.4 use a 'gap template' √3/R taken from the SCALAR spectrum ℓ(ℓ+2)/R², which is consistent with APEX-S3-2. Both state explicitly that it is not a YM mass gap (W066 #3 and W068 #3 are KERNEL_PROVED no-go). Not dependent on A4, but the label 'gap template' should not be read as a gluon threshold.","W056 uses the scalar spectrum l(l+2)/R² correctly."]),
 dict(claim="FBS3R-W036#1", a="A2", work="FBS3R-W036",
   quote="Theorem IV.5 (Natural minimal-redundancy partition). … minimal redundancy, the Fibonacci partition is the unique … spectral coarse-graining of the S³ …",
   refutation="Same as A2 (FBS3R.FibStrat.no_additively_closed_partition_with_ratio_gt_one): the hypothesis class is empty.",
   lean=["FBS3R.FibStrat.no_additively_closed_partition_with_ratio_gt_one"],
   corrected="The Fibonacci intervals partition ℤ≥1 (B30, fib_partition = W036#2, KERNEL_PROVED). Uniqueness is vacuous.",
   corrected_apex=None, corrected_lean_status="KERNEL_PROVED in FBS3R-Lean (B30)",
   deps=[("FBS3R-W036#3","HEURISTIC/PHYSICAL_MODEL","UNSUPPORTED_AFTER_REFUTATION","Glueball hierarchy m_{n+1}/m_n → φ is motivated by the 'natural' Fibonacci bands."),
         ("FBS3R-W036#2","KERNEL_PROVED","unchanged","Partition itself is true.")],
   nondeps=[]),
 dict(claim="FBS3R-W038#0", a="A6", work="FBS3R-W038",
   quote="Theorem 1 (Fibonacci scaling). The shifted sequence (1) [F1 = 3, F2 = 5, F_{n+1} = F_n + F_{n−1}] satisfies F_n = (φ^{n+2} − ψ^{n+2})/√5, so that F_n = φ^{n+2}/√5 + O(φ^{−n}).",
   refutation="At n = 1 the formula gives (φ³ − ψ³)/√5 = 2 ≠ 3 = F₁ (FBS3R.Checks.paper_binet_wrong).",
   lean=["FBS3R.Checks.paper_binet_wrong","FBS3R.Checks.F_binet"],
   corrected="F_n = Fib(n+3) = (φ^{n+3} − ψ^{n+3})/√5 for all n (FBS3R.Checks.F_binet), hence F_n = φ^{n+3}/√5 + O(φ^{−n}). The ratio limit F_{n−1}/F_n → φ^{−1} (eq. 9) remains true.",
   corrected_apex=None, corrected_lean_status="KERNEL_PROVED in FBS3R-Lean (F_binet); no APEX id",
   deps=[("FBS3R-W038 eq. (8) asymptotic (not a separate audit claim)","(part of #0)","CORRECTED: φ^{n+3}/√5","Direct consequence."),
         ("FBS3R-W038#1","KERNEL_PROVED","unchanged","Zero-mode bound uses F_{n−1} as a cardinality, not Binet."),
         ("FBS3R-W038#2","OPEN","OPEN (unaffected)","Schur recursion uses only block sizes.")],
   nondeps=["'Bethe' and the shifted sequence F1 = 3 occur only in W038."]),
 dict(claim="FBS3R-W049#3", a="A7", work="FBS3R-W049",
   quote="The exponential family A_n = A_0 e^{−βn}, β > 0, is admissible, with σ² = (A_0/2π²A³)·e^β(e^β+1)/(e^β−1)³.",
   refutation="Σ_{n≥0}(n+1)² e^{−βn} = e^{2β}(e^β+1)/(e^β−1)³. The stated value is smaller by exactly the factor e^β (FBS3R.CosmoBench.paper_exp_variance_wrong); it is the value for A_n = A_0 e^{−β(n+1)}.",
   lean=["FBS3R.CosmoBench.exp_family_sum","FBS3R.CosmoBench.paper_exp_variance_wrong"],
   corrected="For A_n = A_0 e^{−βn} (β > 0): σ² = (A_0/2π²A³)·e^{2β}(e^β+1)/(e^β−1)³. Equivalently, the paper's expression holds for A_n = A_0 e^{−β(n+1)}. The series identity is kernel-proved (exp_family_sum). The prefactor 1/(2π²A³) is taken from the paper's eq. (variance) and is not formalized.",
   corrected_apex=None, corrected_lean_status="KERNEL_PROVED in FBS3R-Lean (exp_family_sum)",
   deps=[("FBS3R-W049#2","KERNEL_PROVED","unchanged","Power-law part of the same corollary is correct."),
         ("FBS3R-W049#4","HEURISTIC/PHYSICAL_MODEL","unchanged (check any numeric use of σ² for the exponential family)","Manifest does not reference cor:spectra.")],
   nondeps=["cor:spectra is referenced nowhere else in the supplement or the main .tex. 'Benchmark' in W055, W081, W082, W095, W096 refers to unrelated benchmarks."]),
]

def build():
    os.makedirs(f"{OUT}/corrections", exist_ok=True)
    entries = []
    vocab = collections.Counter()
    opens = []; refs = []
    for w in AUD:
        for i, c in enumerate(w["claims"]):
            vocab[c["status"]] += 1
            if c["status"] == "OPEN": opens.append((w, i, c))
            if c["status"] == "DISPROVED": refs.append((w, i, c))
    assert len(opens) == 63 and len(refs) == 8, (len(opens), len(refs))
    for w, i, c in opens:
        p = P[(w["id"], i)]
        for d in p["apex_deps"]: assert d in APEX, d
        entries.append(dict(claim_id=f"{w['id']}#{i}", work_id=w["id"], work_title=w["title"],
            work_file=w["file"], audit_status="OPEN", text_original=c["text"], audit_ref=c.get("ref"),
            statement=p["statement_en"], classification=p["cls"], a_subtarget=p["a_subtarget"],
            next_step=p["next_step"], lean_target=p["lean_target"],
            depends_on_apex=p["apex_deps"], depends_on_fbs3r_lean=p["fbs3r_deps"],
            priority=p["priority"], proposed_status=p["proposed_status"] or "OPEN (unchanged)",
            proved_now=False))
    assert len(P) == 63
    json.dump(dict(generated="2026-11-28", source="APEX/Audit/ARCHIVE_AUDIT.json (pass 2)",
        status_vocabulary=dict(vocab), counts=dict(open=len(opens), refuted_DISPROVED=len(refs)),
        class_legend={"A":"provable now in Lean with Mathlib-level tools","B":"needs substantial new library","C":"genuinely open research / Millennium-level","D":"ill-posed / not a mathematical statement: reformulate","E":"empirical/numerical: needs a certificate script"},
        note="No entry is marked proved: no APEX Lean id proves any OPEN claim exactly. Lean targets are proposals and were not compiled.",
        entries=entries), open(f"{OUT}/CLOSURE_PLAN.json","w"), ensure_ascii=False, indent=1)

    # propagation
    prop = []
    for r in REF:
        wid, idx = r["claim"].split("#"); c = WORK[wid]["claims"][int(idx)]
        assert c["status"] == "DISPROVED"
        prop.append(dict(claim_id=r["claim"], work_id=wid, work_file=WORK[wid]["file"], counterexample_id=r["a"],
            text_original=c["text"], original_quote=r["quote"], refutation=r["refutation"], refuting_lean=r["lean"],
            corrected_statement=r["corrected"], corrected_proved_by_apex=r["corrected_apex"],
            corrected_lean_status=r["corrected_lean_status"],
            dependents=[dict(claim=d[0], current_status=d[1], proposed_status=d[2], reason=d[3]) for d in r["deps"]],
            checked_not_dependent=r["nondeps"]))
    json.dump(dict(generated="2026-11-28", refuted_count=len(prop),
        method="Dependents searched in the audit claims of all 101 works and in full text (pdftotext of all PDFs + .tex) for titles, key terms (stratification, minimal-redundancy, 3/R², √3/R, Φ+, Berry, Binet/F1=3, top-third, Mandelbrot, benchmark spectra/cor:spectra) and cross-citations by the authors.",
        additional_finding="APEX-COL-1 (no_bounded_height_correction) makes the conclusion of W024 Thm 4 (Reduction A') unsatisfiable for any finite state map when required for all odd n > 1, so A' is an empty reduction. This is not caused by A1.",
        refuted=prop), open(f"{OUT}/REFUTED_PROPAGATION.json","w"), ensure_ascii=False, indent=1)

    # markdown plan
    L = ["# Closure plan for open claims in the FBS3R archive (audit pass 2)", "",
         "Date: 2026-11-28. Sources: `APEX/Audit/ARCHIVE_AUDIT.json` (313 claims, 101 works), `APEX_RESULTS.json` (44 APEX results), `Lean/FBS3R-Lean/RESULTS.md` (A1–A7, B1–B70). Nothing was compiled, and no original file was changed.", "",
         "**Status vocabulary in the audit:** " + ", ".join(f"{k} {v}" for k, v in vocab.most_common()) + ". The task's 'open' means `OPEN` (63 claims); 'refuted' means `DISPROVED` (8 claims). Both counts match the expected numbers.", "",
         "**Honesty rule.** No OPEN claim is proved exactly by an APEX Lean id, so none is marked proved. The Lean targets below are proposals and have not been compiled.", "",
         "Classes: **A**: provable now in Lean with Mathlib-level tools · **B**: needs a substantial new library · **C**: genuinely open research problem · **D**: ill-posed, needs reformulation · **E**: numerical, needs a certificate script.", "",
         "Claim id format: `<work-id>#<index in the work's claims[] array>`.", ""]
    cc = collections.Counter(x["classification"] for x in entries)
    L += ["## Counts", "", "| Class | Claims | Priority 1 | Priority 2 | Priority 3 |", "|---|---|---|---|---|"]
    for k in "ABCDE":
        sub = [x for x in entries if x["classification"] == k]
        L.append(f"| {k} | {len(sub)} | " + " | ".join(str(sum(1 for x in sub if x['priority']==p)) for p in (1,2,3)) + " |")
    L.append(f"| **total** | **{len(entries)}** | | | |"); L.append("")
    names = {"A":"Class A: provable now (next Lean targets)","B":"Class B: needs a new library","C":"Class C: open research","D":"Class D: ill-posed, reformulate","E":"Class E: numerical certificate"}
    for k in "ABCDE":
        for p in (1,2,3):
            sub = [x for x in entries if x["classification"] == k and x["priority"] == p]
            if not sub: continue
            L += [f"## {names[k]}, priority {p}", "", "| Claim | Statement | Next step | Deps (APEX ids / FBS3R-Lean A,B ids) | Proposed status |", "|---|---|---|---|---|"]
            for x in sub:
                deps = ", ".join(x["depends_on_apex"] + x["depends_on_fbs3r_lean"]) or "—"
                st = x["next_step"].replace("|","\\|")
                if x["a_subtarget"]: st += f" *A-subtarget:* {x['a_subtarget']}"
                L.append(f"| {x['claim_id']} | {x['statement'].replace('|','\\|')} | {st} | {deps} | {x['proposed_status']} |")
            L.append("")
            if k == "A":
                L += ["Proposed Lean statements:", ""]
                for x in sub:
                    L += [f"- **{x['claim_id']}**", "", "```lean", x["lean_target"], "```", ""]
    L += ["## Refuted claims (see REFUTED_PROPAGATION.json and corrections/)", "", "| Claim | Counterexample | Corrected true statement | Dependents with a new status |", "|---|---|---|---|"]
    for r in prop:
        ds = "; ".join(f"{d['claim']} → {d['proposed_status']}" for d in r["dependents"] if d["proposed_status"].startswith(("UNSUPP","DISPROVED","CORRECTED","OPEN (problem)")))
        L.append(f"| {r['claim_id']} | {r['counterexample_id']} | {r['corrected_statement'].replace('|','\\|')} | {ds or '—'} |")
    L.append("")
    open(f"{OUT}/CLOSURE_PLAN.md","w").write("\n".join(L))

    # corrections
    byw = collections.defaultdict(list)
    for r in prop: byw[r["work_id"]].append(r)
    impact = {
     "FBS3R-W005": "The paper does not prove MLC. Its key step (A5) is false, and the alternative route (π₁ = 0 ⇒ local connectivity, claim #2) is false as an implication. MLC remains an open problem. No conclusion of the paper survives except restatements of known facts (connectedness of M, Douady–Hubbard).",
     "FBS3R-W024": "The correct local bounds (B1–B3, APEX-COL-2) are unaffected. Inequality (2), Theorem 1 (conditional descent) and Theorem 5 (Reduction B') must be restated with the integrand 3 − ν₂ in place of 2 + I − ν₂, which strengthens their hypotheses. Reduction A' does not use Prop. 2, but by APEX-COL-1 its certificate cannot exist when it is required for all odd n > 1. The paper's statement that 'either reduction implies Collatz' therefore holds only in the weak sense that B' is a sufficient (and essentially Collatz-equivalent) hypothesis. The paper never claimed convergence, and Collatz remains open.",
     "FBS3R-W034": "The headline conclusion ('Bell violations are a geometric theorem about S³, filled by the unique Fibonacci stratification') loses both pillars. Uniqueness (Thm 4.5) is vacuous (A2). Hyperconnectivity (Def. 4.7 / Thm 4.8) requires F_k = F_m + F_n, which is false. The Berry-phase kernel (Thm 3.3 / §5.1) is wrong for Φ⁺ (A3). What survives: CHSH ≤ 2 for LHV (B25), the singlet Tsirelson kernel (B26), the Fibonacci partition (B30), and the corrected singlet computation as presented in the PRA version W043. Cor. 5.3 and the 'geometric origin' interpretation become UNSUPPORTED_AFTER_REFUTATION.",
     "FBS3R-W036": "Result (2) of the paper (λ₁^V = 3/R², Δ = √3/R, Δ ≈ 520 MeV) is wrong. The transverse threshold of the archive's own curl² spectrum is 4/R² (Δ = 2/R), and 3/R² is the scalar eigenvalue. Result (3) (natural/unique Fibonacci partition) reduces to the true partition statement B30, with uniqueness vacuous (A2). Result (4) (glueball hierarchy, m₃/m₁) inherits both errors and becomes UNSUPPORTED_AFTER_REFUTATION. Any finite-volume threshold → 0 as R → ∞, so the abstract's 'lower bound for the infinite-volume gap' is unsupported (APEX-YM-1, APEX-S3-2). The YM mass gap (Conjecture V.1) stays OPEN.",
     "FBS3R-W038": "Only the exponent changes: F_n = Fib(n+3), with asymptotic φ^{n+3}/√5. The ratio limit φ^{-1}, the zero-mode bound (B36) and the Schur-complement recursions are unaffected. Any downstream numeric use of φ^{n+2}/√5 (e.g. state counts) is low by a factor φ.",
     "FBS3R-W049": "Affects only the supplement's Cor. 'Benchmark spectra'. For A_n = A_0e^{−βn} the point variance is larger by e^β than stated, and admissibility (finiteness) is unchanged. The power-law criterion α > 3 (B62) and the background results (B60–B61) are unaffected. The main PDF does not contain the corollary.",
    }
    for wid, rs in byw.items():
        w = WORK[wid]
        T = [f"# {wid}: corrected scientific edition (errata only)", "",
             f"- **Title:** {w['title']}", f"- **Original path (unchanged):** `{REPO}/{w['file']}`"]
        if wid == "FBS3R-W049":
            T.append(f"- **Erratum location:** `{REPO}/All Preprints/2026_05_11_Benchmark_residual_invariants_in_compact_S3_cosmology/2026_05_11_Benchmark_residual_invariants_in_compact_S3_cosmology_supplement.tex` (Corollary `cor:spectra`, lines ~403–418). This file is unchanged too.")
        T += [f"- **Audit status of the work:** {w['status']} (pass 2)", "- **Prepared:** 2026-11-28 by the APEX auditor. This is not a rewrite of the paper: it lists errata and their consequences only.", "", "## Errata", ""]
        for k, r in enumerate(rs, 1):
            T += [f"### E{k}. {r['claim_id']} ({r['counterexample_id']})", "",
                  "**Original text (quoted from the paper):**", "", f"> {r['original_quote']}", "",
                  f"**Refutation:** {r['refutation']}", "",
                  f"**Corrected statement (true):** {r['corrected_statement']}", "",
                  f"**Justification / Lean:** refuting declarations: {', '.join('`'+x+'`' for x in r['refuting_lean'])}. Corrected statement: {r['corrected_lean_status']}." + (f" APEX: {r['corrected_proved_by_apex']}." if r['corrected_proved_by_apex'] else ""), "",
                  "**Dependent claims:**", ""]
            for d in r["dependents"]:
                T.append(f"- {d['claim']}: {d['current_status']} → **{d['proposed_status']}**. {d['reason']}")
            if r["checked_not_dependent"]:
                T += ["", "**Checked, not dependent:** " + " ".join(r["checked_not_dependent"])]
            T.append("")
        T += ["## Impact on the work's conclusions", "", impact[wid], ""]
        open(f"{OUT}/corrections/{wid}_CORRECTED.md","w").write("\n".join(T))
    return entries, prop, cc

if __name__ == "__main__":
    entries, prop, cc = build()
    print(dict(cc), len(entries), len(prop))
