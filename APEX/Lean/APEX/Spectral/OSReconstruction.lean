import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Abstract Osterwalder–Schrader reconstruction step (transfer matrix)

**Setting (real, purely algebraic; no finite-dimensionality needed).** `V` is a real vector
space (time-zero-supported observables `F`), `b : V →ₗ V →ₗ ℝ` a bilinear form
(`b F G = ⟨θF, G⟩`), and `S : V →ₗ V` (unit Euclidean time translation), bundled in `OSData`
with exactly these hypotheses:
* `symm`  : `b F G = b G F` (symmetric / real-Hermitian);
* `pos`   : `0 ≤ b F F` (**reflection positivity**, `⟨θF,F⟩ ≥ 0`);
* `S_symm`: `b F (S G) = b (S F) G` (`S` is `b`-symmetric);
* `S_pos` : `0 ≤ b F (S F)` (**one-step reflection positivity**, `⟨θF, S F⟩ ≥ 0`, which holds
  when RP is available for reflections through the planes half-way between time slices as
  well; with only site-plane RP one gets it for `S²` only).
The boundedness hypothesis used in §3 is `OrbitBdd`: for every `F` there is `M` with
`b F (Sⁿ F) ≤ M` for all `n` (implied by `sup_n |b(F, Sⁿ F)| < ∞`, e.g. for a
translation-invariant Euclidean measure with bounded correlations).

**Results.**
1. `cauchy_schwarz`: `b(F,G)² ≤ b(F,F) b(G,G)`. The null space `N := ker b` satisfies
   `coe_N : (N : Set V) = {F | b F F = 0}` (so `{F | b(F,F)=0}` is a subspace) and
   `S_maps_N : N ≤ N.comap S`.
2. On `H := V ⧸ N`: the induced form `bq` (`bq_mk : bq [F] [G] = b F G`) is symmetric
   (`bq_symm`), positive definite (`bq_pos`, `bq_definite`); `S` induces `T := N.mapQ N S`
   (`T_mk`), which is `bq`-symmetric (`T_symm`) and positive (`T_pos`).
3. `os_iteration` (Cauchy–Schwarz iteration, integer-power form of
   `⟨ψ,Tψ⟩ ≤ ‖ψ‖^{2(1-2^{-n})} ⟨ψ,T^{2^n}ψ⟩^{2^{-n}}`):
   `‖ψ‖² · ⟨ψ,Tψ⟩^{2^n} ≤ ‖ψ‖^{2·2^n} · ⟨ψ,T^{2^n}ψ⟩` with `‖ψ‖² = bq ψ ψ`.
   Under `OrbitBdd`: `T_le_one` (`0 ≤ ⟨ψ,Tψ⟩ ≤ ‖ψ‖²`, i.e. `0 ≤ T ≤ 1`), `T_norm_le`
   (`‖Tψ‖² ≤ ‖ψ‖²`, i.e. `‖T‖ ≤ 1`), `T_eigenvalue_mem` (every eigenvalue of `T` lies in
   `[0,1]`).
4. `transfer_form`: `b F (Sⁿ G) = bq [F] (Tⁿ [G])`.
5. `spectrum_perp_vacuum`: if `|b(F,SⁿG) − b(F,Ω) b(Ω,G)| ≤ C_{F,G} e^{−Δn}` for all `n`
   (clustering, for a vacuum vector `Ω`), then every eigenvalue `λ` of `T` with an eigenvector
   `ψ ≠ 0`, `bq [Ω] ψ = 0` satisfies `0 ≤ λ ≤ e^{−Δ}`. This is exactly the hypothesis `hspec`
   of `APEX.YM.transfer_bound` (with lattice spacing `a = 1`), stated for the form `bq`.
   *Not done:* equipping `H` with a (complex) `InnerProductSpace` instance so that
   `APEX.YM.SpectralGap` applies literally; the complex (sesquilinear) case.

**Scope / caveat.** This is the abstract algebraic reconstruction step only. Verifying
reflection positivity (`pos`, `S_pos`), the orbit bound, and above all the clustering bound
with `Δ > 0` **uniformly in the lattice spacing `a` and volume `L`** for 4D SU(2) lattice
Yang–Mills (or any QG model) is **NOT** done here; those are the hard, open inputs.
-/

namespace APEX.Spectral.OSReconstruction

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Osterwalder–Schrader data. -/
structure OSData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  S : V →ₗ[ℝ] V
  symm : ∀ F G, b F G = b G F
  pos : ∀ F, 0 ≤ b F F
  S_symm : ∀ F G, b F (S G) = b (S F) G
  S_pos : ∀ F, 0 ≤ b F (S F)

/-- Bounded orbits: `b(F, Sⁿ F)` is bounded above in `n`, for each `F`. -/
def OSData.OrbitBdd (D : OSData V) : Prop := ∀ F, ∃ M : ℝ, ∀ n : ℕ, D.b F ((D.S ^ n) F) ≤ M

namespace OSData

variable (D : OSData V)

/-! ### 1. Cauchy–Schwarz and the null space -/

theorem cauchy_schwarz (F G : V) : D.b F G ^ 2 ≤ D.b F F * D.b G G := by
  have h : ∀ t : ℝ, 0 ≤ D.b G G * (t * t) + 2 * D.b F G * t + D.b F F := fun t => by
    have e : D.b (F + t • G) (F + t • G) = D.b G G * (t * t) + 2 * D.b F G * t + D.b F F := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [D.symm G F]; ring
    rw [← e]; exact D.pos _
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith

/-- The null space `N = ker b`. -/
def N : Submodule ℝ V := LinearMap.ker D.b

theorem mem_N_iff {F : V} : F ∈ D.N ↔ D.b F F = 0 := by
  constructor
  · intro h; rw [N, LinearMap.mem_ker] at h; simp [h]
  · intro h
    rw [N, LinearMap.mem_ker]
    refine LinearMap.ext fun G => ?_
    have h2 : D.b F G ^ 2 = 0 :=
      le_antisymm (by nlinarith [D.cauchy_schwarz F G, D.pos G]) (sq_nonneg _)
    simpa using h2

/-- `{F | b(F,F) = 0}` is (the carrier of) a subspace. -/
theorem coe_N : (D.N : Set V) = {F | D.b F F = 0} := by
  ext F; exact D.mem_N_iff

lemma b_left_N {n : V} (hn : n ∈ D.N) (G : V) : D.b n G = 0 := by
  rw [N, LinearMap.mem_ker] at hn; simp [hn]

lemma b_right_N {n : V} (hn : n ∈ D.N) (F : V) : D.b F n = 0 := by
  rw [D.symm]; exact D.b_left_N hn F

/-- `S` maps `N` into `N`. -/
theorem S_maps_N : D.N ≤ D.N.comap D.S := by
  intro n hn
  rw [Submodule.mem_comap, N, LinearMap.mem_ker]
  refine LinearMap.ext fun G => ?_
  rw [LinearMap.zero_apply, ← D.S_symm]
  exact D.b_left_N hn _

/-! ### 2. The quotient Hilbert (pre-)space and the transfer matrix -/

/-- First-argument descent. -/
def b₁ : V ⧸ D.N →ₗ[ℝ] V →ₗ[ℝ] ℝ := D.N.liftQ D.b le_rfl

lemma b₁_flip_N : D.N ≤ LinearMap.ker D.b₁.flip := by
  intro n hn
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective D.N ψ
  simp only [LinearMap.flip_apply, LinearMap.zero_apply, b₁]
  exact D.b_right_N hn F

/-- The induced form on `H = V ⧸ N`. -/
def bq : V ⧸ D.N →ₗ[ℝ] V ⧸ D.N →ₗ[ℝ] ℝ := (D.N.liftQ D.b₁.flip D.b₁_flip_N).flip

@[simp] theorem bq_mk (F G : V) :
    D.bq (Submodule.Quotient.mk F) (Submodule.Quotient.mk G) = D.b F G := by
  simp only [bq, b₁, LinearMap.flip_apply, Submodule.liftQ_apply]
  rfl

theorem bq_symm (ψ φ : V ⧸ D.N) : D.bq ψ φ = D.bq φ ψ := by
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective D.N ψ
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective D.N φ
  simp [D.symm F G]

theorem bq_pos (ψ : V ⧸ D.N) : 0 ≤ D.bq ψ ψ := by
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective D.N ψ
  simpa using D.pos F

theorem bq_definite {ψ : V ⧸ D.N} (h : D.bq ψ ψ = 0) : ψ = 0 := by
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective D.N ψ
  rw [Submodule.Quotient.mk_eq_zero, D.mem_N_iff]
  simpa using h

/-- The transfer matrix `T` induced by `S` on `H`. -/
def T : V ⧸ D.N →ₗ[ℝ] V ⧸ D.N := D.N.mapQ D.N D.S D.S_maps_N

@[simp] theorem T_mk (F : V) :
    D.T (Submodule.Quotient.mk F) = Submodule.Quotient.mk (D.S F) := by
  simp [T, Submodule.mapQ_apply]

theorem T_pow_mk (n : ℕ) (F : V) :
    (D.T ^ n) (Submodule.Quotient.mk F) = Submodule.Quotient.mk ((D.S ^ n) F) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, T_mk, pow_succ', mul_apply_eq_comp]

theorem T_symm (ψ φ : V ⧸ D.N) : D.bq ψ (D.T φ) = D.bq (D.T ψ) φ := by
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective D.N ψ
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective D.N φ
  simp [D.S_symm F G]

theorem T_pos (ψ : V ⧸ D.N) : 0 ≤ D.bq ψ (D.T ψ) := by
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective D.N ψ
  simpa using D.S_pos F

/-! ### 4. Transfer form -/

/-- **Transfer form.** `b(F, Sⁿ G) = ⟨[F], Tⁿ [G]⟩`. -/
theorem transfer_form (n : ℕ) (F G : V) :
    D.b F ((D.S ^ n) G) =
      D.bq (Submodule.Quotient.mk F) ((D.T ^ n) (Submodule.Quotient.mk G)) := by
  rw [T_pow_mk, bq_mk]

/-! ### 3. Cauchy–Schwarz iteration and `0 ≤ T ≤ 1` -/

/-- Powers of a `b`-symmetric map are `b`-symmetric. -/
lemma pow_symm {R : V →ₗ[ℝ] V} (hR : ∀ F G, D.b F (R G) = D.b (R F) G) (k : ℕ) (F G : V) :
    D.b ((R ^ k) F) G = D.b F ((R ^ k) G) := by
  induction k generalizing F G with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, ← hR, ← mul_apply_eq_comp, ← pow_succ', pow_succ]

/-- **OS Cauchy–Schwarz iteration** on `V`, for any `b`-symmetric `R`:
`b(F,F) · b(F,RF)^{2^n} ≤ b(F,F)^{2^n} · b(F, R^{2^n} F)`. -/
theorem iteration_V {R : V →ₗ[ℝ] V} (hR : ∀ F G, D.b F (R G) = D.b (R F) G)
    (hRp : ∀ F, 0 ≤ D.b F (R F)) (F : V) (n : ℕ) :
    D.b F F * D.b F (R F) ^ (2 ^ n) ≤ D.b F F ^ (2 ^ n) * D.b F ((R ^ (2 ^ n)) F) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set N0 := D.b F F
    set x := D.b F (R F)
    set m := 2 ^ n
    have hN0 := D.pos F
    have hx := hRp F
    have hcs : D.b F ((R ^ m) F) ^ 2 ≤ N0 * D.b F ((R ^ (m + m)) F) := by
      have := D.cauchy_schwarz F ((R ^ m) F)
      rwa [D.pow_symm hR, ← mul_apply_eq_comp, ← pow_add] at this
    have hL : 0 ≤ N0 * x ^ m := by positivity
    have hsq : (N0 * x ^ m) ^ 2 ≤ (N0 ^ m * D.b F ((R ^ m) F)) ^ 2 :=
      pow_le_pow_left₀ hL ih 2
    have h2 : N0 * (N0 * x ^ (2 ^ (n + 1))) ≤ N0 * (N0 ^ (2 ^ (n + 1)) *
        D.b F ((R ^ (2 ^ (n + 1))) F)) := by
      have e1 : (2 : ℕ) ^ (n + 1) = m + m := by rw [pow_succ]; ring
      rw [e1]
      have : (N0 ^ m * D.b F ((R ^ m) F)) ^ 2 ≤ N0 ^ (m + m) * (N0 * D.b F ((R ^ (m + m)) F)) := by
        rw [mul_pow, ← pow_mul, mul_two]
        exact mul_le_mul_of_nonneg_left hcs (by positivity)
      calc N0 * (N0 * x ^ (m + m)) = (N0 * x ^ m) ^ 2 := by ring
        _ ≤ _ := hsq.trans this
        _ = _ := by ring
    rcases hN0.lt_or_eq with hpos | hzero
    · exact le_of_mul_le_mul_left h2 hpos
    · have h0 : N0 = 0 := hzero.symm
      rw [h0]; simp

/-- From bounded dyadic orbits: `b(F,RF) ≤ b(F,F)`. -/
theorem le_of_iteration {R : V →ₗ[ℝ] V} (hR : ∀ F G, D.b F (R G) = D.b (R F) G)
    (hRp : ∀ F, 0 ≤ D.b F (R F)) (F : V) (M : ℝ)
    (hM : ∀ n : ℕ, D.b F ((R ^ (2 ^ n)) F) ≤ M) :
    D.b F (R F) ≤ D.b F F := by
  have hN0 := D.pos F
  rcases hN0.lt_or_eq with hpos | hzero
  · by_contra hlt
    push Not at hlt
    set r := D.b F (R F) / D.b F F
    have hr : 1 < r := (one_lt_div hpos).2 hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (M / D.b F F) hr
    have hit := D.iteration_V hR hRp F k
    have hle : r ^ k ≤ r ^ (2 ^ k) := pow_le_pow_right₀ hr.le Nat.lt_two_pow_self.le
    have : r ^ (2 ^ k) ≤ M / D.b F F := by
      rw [le_div_iff₀ hpos, div_pow]
      have hp : 0 < D.b F F ^ (2 ^ k) := pow_pos hpos _
      rw [div_mul_eq_mul_div, div_le_iff₀ hp]
      have := (hit.trans (mul_le_mul_of_nonneg_left (hM k) hp.le))
      linarith
    linarith
  · have hcs := D.cauchy_schwarz F (R F)
    rw [← hzero, zero_mul] at hcs
    have : D.b F (R F) = 0 := by nlinarith [sq_nonneg (D.b F (R F))]
    rw [this, ← hzero]

/-- **OS iteration on `H`.** `‖ψ‖² ⟨ψ,Tψ⟩^{2^n} ≤ ‖ψ‖^{2·2^n} ⟨ψ, T^{2^n} ψ⟩`. -/
theorem os_iteration (ψ : V ⧸ D.N) (n : ℕ) :
    D.bq ψ ψ * D.bq ψ (D.T ψ) ^ (2 ^ n) ≤ D.bq ψ ψ ^ (2 ^ n) * D.bq ψ ((D.T ^ (2 ^ n)) ψ) := by
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective D.N ψ
  rw [T_mk, T_pow_mk, bq_mk, bq_mk, bq_mk]
  exact D.iteration_V D.S_symm D.S_pos F n

/-- **`0 ≤ T ≤ 1`.** -/
theorem T_le_one (hb : D.OrbitBdd) (ψ : V ⧸ D.N) :
    0 ≤ D.bq ψ (D.T ψ) ∧ D.bq ψ (D.T ψ) ≤ D.bq ψ ψ := by
  refine ⟨D.T_pos ψ, ?_⟩
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective D.N ψ
  obtain ⟨M, hM⟩ := hb F
  rw [T_mk, bq_mk, bq_mk]
  exact D.le_of_iteration D.S_symm D.S_pos F M fun n => hM _

/-- **`‖T‖ ≤ 1`:** `‖Tψ‖² ≤ ‖ψ‖²` (apply the iteration to `S²`). -/
theorem T_norm_le (hb : D.OrbitBdd) (ψ : V ⧸ D.N) : D.bq (D.T ψ) (D.T ψ) ≤ D.bq ψ ψ := by
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective D.N ψ
  obtain ⟨M, hM⟩ := hb F
  rw [T_mk, bq_mk, bq_mk]
  have hR : ∀ F G, D.b F ((D.S ^ 2) G) = D.b ((D.S ^ 2) F) G := fun F G =>
    (D.pow_symm D.S_symm 2 F G).symm
  have hRp : ∀ F, 0 ≤ D.b F ((D.S ^ 2) F) := fun F => by
    rw [pow_two, mul_apply_eq_comp, D.S_symm]; exact D.pos _
  have h := D.le_of_iteration hR hRp F M fun n => by rw [← pow_mul]; exact hM _
  rw [← D.S_symm]
  rw [pow_two, mul_apply_eq_comp] at h
  exact h

/-- **Eigenvalues of `T` lie in `[0,1]`.** -/
theorem T_eigenvalue_mem (hb : D.OrbitBdd) {ψ : V ⧸ D.N} (hψ : ψ ≠ 0) {lam : ℝ}
    (hT : D.T ψ = lam • ψ) : 0 ≤ lam ∧ lam ≤ 1 := by
  have hp : 0 < D.bq ψ ψ := lt_of_le_of_ne (D.bq_pos ψ) fun h => hψ (D.bq_definite h.symm)
  obtain ⟨h0, h1⟩ := D.T_le_one hb ψ
  rw [hT, map_smul, smul_eq_mul] at h0 h1
  constructor
  · exact nonneg_of_mul_nonneg_left h0 hp
  · nlinarith

/-! ### 5. Clustering ⇒ spectrum of `T` on `Ω^⊥` in `[0, e^{-Δ}]` -/

lemma T_pow_eigen {ψ : V ⧸ D.N} {lam : ℝ} (hT : D.T ψ = lam • ψ) (n : ℕ) :
    (D.T ^ n) ψ = lam ^ n • ψ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hT, smul_smul, pow_succ]

/-- **Spectral gap from clustering.** If `|b(F,SⁿG) − b(F,Ω)b(Ω,G)| ≤ C e^{−Δn}` for all `n`,
then every eigenvalue of `T` on `[Ω]^⊥` lies in `[0, e^{−Δ}]` (`hspec` form of
`APEX.YM.transfer_bound` with `a = 1`). No orbit bound is needed. -/
theorem spectrum_perp_vacuum (Ω : V) (Δ : ℝ)
    (hclust : ∀ F G : V, ∃ C : ℝ, ∀ n : ℕ,
      |D.b F ((D.S ^ n) G) - D.b F Ω * D.b Ω G| ≤ C * Real.exp (-(Δ * n)))
    (ψ : V ⧸ D.N) (lam : ℝ) (hψ : ψ ≠ 0) (hΩ : D.bq (Submodule.Quotient.mk Ω) ψ = 0)
    (hT : D.T ψ = lam • ψ) : 0 ≤ lam ∧ lam ≤ Real.exp (-Δ) := by
  have hp : 0 < D.bq ψ ψ := lt_of_le_of_ne (D.bq_pos ψ) fun h => hψ (D.bq_definite h.symm)
  have h0 : 0 ≤ lam := by
    have := D.T_pos ψ
    rw [hT, map_smul, smul_eq_mul] at this
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨h0, ?_⟩
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective D.N ψ
  rw [bq_mk] at hΩ
  obtain ⟨C, hC⟩ := hclust F F
  have hn : ∀ n : ℕ, (lam * Real.exp Δ) ^ n ≤ C / D.b F F := by
    intro n
    have h := hC n
    rw [hΩ, mul_zero, sub_zero, transfer_form, T_pow_eigen D hT, map_smul, smul_eq_mul,
      bq_mk] at h
    have h' : lam ^ n * D.b F F ≤ C * Real.exp (-(Δ * n)) := (le_abs_self _).trans h
    rw [le_div_iff₀ (by simpa using hp), mul_pow, ← Real.exp_nat_mul]
    have he : Real.exp (n * Δ) * Real.exp (-(Δ * n)) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have hep : 0 < Real.exp (n * Δ) := Real.exp_pos _
    calc lam ^ n * Real.exp (n * Δ) * D.b F F = Real.exp (n * Δ) * (lam ^ n * D.b F F) := by ring
      _ ≤ Real.exp (n * Δ) * (C * Real.exp (-(Δ * n))) := mul_le_mul_of_nonneg_left h' hep.le
      _ = C := by rw [mul_left_comm, he, mul_one]
  by_contra hlt
  push Not at hlt
  have hr : 1 < lam * Real.exp Δ := by
    have := mul_lt_mul_of_pos_right hlt (Real.exp_pos Δ)
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / D.b F F) hr
  linarith [hn k]

end OSData

end APEX.Spectral.OSReconstruction

