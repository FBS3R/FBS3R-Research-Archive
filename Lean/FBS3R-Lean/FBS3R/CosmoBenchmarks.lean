/-
# Residual-cosmology benchmarks (2026-05-10 … 2026-05-19)

Sources: *Benchmark residual invariants in compact S³ cosmology* (2026-05-11, with its
supplement), *Dark-Sector Residuals* (2026-05-10), *Γ Topological Residual Cosmology*
(2026-05-13), *Spherical FLRW Residuals* (2026-05-15), *Residual-First Standard* and
*Einstein Residual Closure Standard* (2026-05-19).

Machine-checked here:
* `residual_unique`, `residual_convention` : `G = κ(T_vis + S)` forces `S = G/κ − T_vis`;
  shifting `T_vis` by `X` shifts the residual by `−X` (any real vector space of tensors).
* `closure_criterion` : on an open interval, `(ε, p)` has the dust-plus-vacuum form
  `ε = ε_w a⁻³ + ε_q`, `p = −ε_q` **iff** `p' = 0` and `(a³(ε + p))' = 0`.
* `einstein_static` : `F(a) = Ω_m/a + Ω_Λ a² − |Ω_K|` with `F = F' = 0` gives
  `Ω_m = 2Ω_Λ a³`, `a² = |Ω_K|/(3Ω_Λ)`, and linearised coefficient `F''/2 = 3Ω_Λ`.
* `acceleration_boundary` : `ä = 0 ⇔ a³ = Ω_m/(2Ω_Λ)`.
* `turning_point` : for `w ≠ −1/3`, `Ω a^{−3(1+w)} = |Ω_K| a^{−2} ⇔ a = (Ω/|Ω_K|)^{1/(1+3w)}`.
* `power_law_admissible` : `Σ (n+1)²(n+1)^{−α} < ∞ ⇔ α > 3`.
* `exp_family_sum` : `Σ_{n≥0} (n+1)² e^{−βn} = e^{2β}(e^β+1)/(e^β−1)³`.
* **Error found** (`paper_exp_variance_wrong`): the supplement states
  `σ² = (A₀/2π²A³) · e^β(e^β+1)/(e^β−1)³` for `A_n = A₀e^{−βn}`; the correct factor is
  `e^{2β}(e^β+1)/(e^β−1)³` — the paper's value is too small by the factor `e^β`
  (it corresponds to `A_n = A₀e^{−β(n+1)}`).
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace FBS3R.CosmoBench

open Real Set

section Residual
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem residual_unique (κ : ℝ) (hκ : κ ≠ 0) (G T S : V) (h : G = κ • (T + S)) :
    S = κ⁻¹ • G - T := by
  rw [h, smul_smul, inv_mul_cancel₀ hκ, one_smul]; abel

theorem residual_convention (κ : ℝ) (hκ : κ ≠ 0) (G T X : V) :
    κ⁻¹ • G - (T + X) = (κ⁻¹ • G - T) - X := by abel

end Residual

/-- **Homogeneous closure criterion** (dust + fixed vacuum). -/
theorem closure_criterion (I : Set ℝ) (hI : IsOpen I) (hc : IsPreconnected I)
    (hpos : ∀ a ∈ I, 0 < a) (ε p : ℝ → ℝ)
    (hε : DifferentiableOn ℝ ε I) (hp : DifferentiableOn ℝ p I) :
    (∃ εw εq : ℝ, ∀ a ∈ I, ε a = εw * a⁻¹ ^ 3 + εq ∧ p a = -εq) ↔
      (∀ a ∈ I, deriv p a = 0 ∧ deriv (fun b => b ^ 3 * (ε b + p b)) a = 0) := by
  constructor
  · rintro ⟨εw, εq, h⟩ a ha
    have hnhds : I ∈ nhds a := hI.mem_nhds ha
    have ep : p =ᶠ[nhds a] fun _ => -εq :=
      Filter.eventually_of_mem hnhds fun b hb => (h b hb).2
    have ee : (fun b => b ^ 3 * (ε b + p b)) =ᶠ[nhds a] fun _ => εw := by
      apply Filter.eventually_of_mem hnhds; intro b hb
      have hb0 : b ≠ 0 := (hpos b hb).ne'
      simp only [(h b hb).1, (h b hb).2]; field_simp; ring
    exact ⟨by rw [ep.deriv_eq]; simp, by rw [ee.deriv_eq]; simp⟩
  · intro h
    by_cases hne : I.Nonempty
    · obtain ⟨a₀, ha₀⟩ := hne
      have hdiffg : DifferentiableOn ℝ (fun b => b ^ 3 * (ε b + p b)) I :=
        ((differentiableOn_id.pow 3)).mul (hε.add hp)
      obtain ⟨cq, hcq⟩ := hI.exists_is_const_of_deriv_eq_zero hc hp fun a ha => (h a ha).1
      obtain ⟨cw, hcw⟩ := hI.exists_is_const_of_deriv_eq_zero hc hdiffg fun a ha => (h a ha).2
      refine ⟨cw, -cq, fun a ha => ⟨?_, by rw [hcq a ha]; ring⟩⟩
      have h1 := hcw a ha
      have h2 := hcq a ha
      have ha0 : a ≠ 0 := (hpos a ha).ne'
      rw [h2] at h1
      field_simp
      linear_combination h1
    · exact ⟨0, 0, fun a ha => absurd ⟨a, ha⟩ hne⟩

/-- **Einstein static benchmark.** -/
theorem einstein_static (Ωm ΩΛ K a : ℝ) (ha : 0 < a) (hΛ : 0 < ΩΛ)
    (hF : Ωm / a + ΩΛ * a ^ 2 - K = 0) (hF' : -Ωm / a ^ 2 + 2 * ΩΛ * a = 0) :
    Ωm = 2 * ΩΛ * a ^ 3 ∧ a ^ 2 = K / (3 * ΩΛ) ∧ (2 * Ωm / a ^ 3 + 2 * ΩΛ) / 2 = 3 * ΩΛ := by
  have ha0 : a ≠ 0 := ha.ne'
  have hm : Ωm = 2 * ΩΛ * a ^ 3 := by field_simp at hF'; linarith
  refine ⟨hm, ?_, ?_⟩
  · rw [hm] at hF; field_simp at hF ⊢; linarith
  · rw [hm]; field_simp; ring

/-- **Acceleration boundary** (dust + Λ): `ä ∝ −Ω_m/a² + 2Ω_Λ a = 0 ⇔ a³ = Ω_m/(2Ω_Λ)`. -/
theorem acceleration_boundary (Ωm ΩΛ a : ℝ) (ha : 0 < a) (hΛ : 0 < ΩΛ) :
    -Ωm / a ^ 2 + 2 * ΩΛ * a = 0 ↔ a ^ 3 = Ωm / (2 * ΩΛ) := by
  have ha0 : a ≠ 0 := ha.ne'
  constructor
  · intro h; field_simp at h ⊢; linarith
  · intro h; field_simp at h ⊢; linarith

/-- **Turning point** for a single residual plus curvature. -/
theorem turning_point (Ω K w a : ℝ) (hΩ : 0 < Ω) (hK : 0 < K) (ha : 0 < a)
    (hw : 1 + 3 * w ≠ 0) :
    Ω * a ^ (-3 * (1 + w)) = K * a ^ (-2 : ℝ) ↔ a = (Ω / K) ^ (1 / (1 + 3 * w)) := by
  have key : Ω * a ^ (-3 * (1 + w)) = K * a ^ (-2 : ℝ) ↔ a ^ (1 + 3 * w) = Ω / K := by
    have hsplit : a ^ (-2 : ℝ) = a ^ (1 + 3 * w) * a ^ (-3 * (1 + w)) := by
      rw [← rpow_add ha]; ring_nf
    have hX : 0 < a ^ (-3 * (1 + w)) := rpow_pos_of_pos ha _
    rw [hsplit, eq_div_iff hK.ne']
    constructor
    · intro h
      have : Ω * a ^ (-3 * (1 + w)) = (K * a ^ (1 + 3 * w)) * a ^ (-3 * (1 + w)) := by
        rw [h]; ring
      have := mul_right_cancel₀ hX.ne' this
      linarith
    · intro h; rw [← h]; ring
  rw [key]
  constructor
  · intro h; rw [← h, ← rpow_mul ha.le, mul_one_div_cancel hw, rpow_one]
  · intro h; rw [h, ← rpow_mul (div_pos hΩ hK).le, one_div_mul_cancel hw, rpow_one]

/-- **Power-law admissibility**: finite point variance iff `α > 3`. -/
theorem power_law_admissible (α : ℝ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ (-α)) ↔ 3 < α := by
  have e : (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ (-α))
      = fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (2 - α) := by
    ext n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    push_cast
    rw [rpow_sub hn, rpow_two, rpow_neg hn.le]; field_simp
  rw [e, summable_nat_add_iff 1 (f := fun n : ℕ => (n : ℝ) ^ (2 - α)), summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-- `Σ_{n≥0} (n+1)² xⁿ = (1+x)/(1−x)³` for `|x| < 1`. -/
theorem hasSum_sq_geometric (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * x ^ n) ((1 + x) / (1 - x) ^ 3) := by
  have hx' : ‖x‖ < 1 := by simpa using hx
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hx'
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hx'
  have h := (h2.mul_left 2).sub h1
  have hne : (1 - x) ≠ 0 := by
    have := (abs_lt.mp hx).2; linarith
  convert h using 1
  · ext n
    have c2 : ∀ m : ℕ, ((m + 2).choose 2 : ℝ) = (m + 2) * (m + 1) / 2 := by
      intro m
      induction m with
      | zero => norm_num
      | succ k ih =>
        rw [show k + 1 + 2 = (k + 2) + 1 from rfl, Nat.choose_succ_succ]
        push_cast; rw [ih, Nat.choose_one_right]; push_cast; ring
    have c2 := c2 n
    have c1 : ((n + 1).choose 1 : ℝ) = n + 1 := by simp
    rw [c2, c1]; ring
  · field_simp; ring

/-- `Σ_{n≥0} (n+1)² e^{−βn} = e^{2β}(e^β+1)/(e^β−1)³`. -/
theorem exp_family_sum (β : ℝ) (hβ : 0 < β) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * exp (-β * n))
      (exp (2 * β) * (exp β + 1) / (exp β - 1) ^ 3) := by
  have hx : |exp (-β)| < 1 := by
    rw [abs_of_pos (exp_pos _)]; rw [← exp_zero]; exact exp_lt_exp.mpr (by linarith)
  have h := hasSum_sq_geometric (exp (-β)) hx
  have he : 1 < exp β := one_lt_exp_iff.mpr hβ
  convert h using 1
  · ext n; rw [← exp_nat_mul]; ring_nf
  · have h1 : exp (-β) = (exp β)⁻¹ := by rw [exp_neg]
    have h2 : exp (2 * β) = exp β ^ 2 := by rw [← exp_nat_mul]; norm_num
    rw [h1, h2]
    have : exp β - 1 ≠ 0 := by linarith
    have : exp β ≠ 0 := (exp_pos β).ne'
    field_simp

/-- **Error in the 2026-05-11 supplement**: the stated factor `e^β(e^β+1)/(e^β−1)³`
is not the sum `Σ (n+1)² e^{−βn}`; it is smaller by exactly `e^β`. -/
theorem paper_exp_variance_wrong (β : ℝ) (hβ : 0 < β) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * exp (-β * n)
      = exp β * (exp β * (exp β + 1) / (exp β - 1) ^ 3) ∧
    ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * exp (-β * n) ≠ exp β * (exp β + 1) / (exp β - 1) ^ 3 := by
  have h := (exp_family_sum β hβ).tsum_eq
  have he : 1 < exp β := one_lt_exp_iff.mpr hβ
  have h2 : exp (2 * β) = exp β * exp β := by rw [← exp_add]; ring_nf
  refine ⟨by rw [h, h2]; ring, ?_⟩
  rw [h, h2]
  intro heq
  have hpos : 0 < exp β * (exp β + 1) / (exp β - 1) ^ 3 := by
    apply div_pos (by positivity); apply pow_pos; linarith
  have key : exp β * exp β * (exp β + 1) / (exp β - 1) ^ 3
      = exp β * (exp β * (exp β + 1) / (exp β - 1) ^ 3) := by ring
  rw [key] at heq
  have h1 : exp β * (exp β * (exp β + 1) / (exp β - 1) ^ 3)
      = 1 * (exp β * (exp β + 1) / (exp β - 1) ^ 3) := by rw [one_mul]; exact heq
  have := mul_right_cancel₀ hpos.ne' h1
  linarith

end FBS3R.CosmoBench
