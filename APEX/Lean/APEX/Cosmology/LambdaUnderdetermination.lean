import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Trace-free (unimodular) gravity does not fix Λ, and convex selectors do not fix q

This file is a formal audit of the *local* mechanism of the FBS3R preprints of
2026-08-10/11/12/17 (trace-free gravity with a "capacity" assignment
`Λ = 3π/(ℓ_P² q)` and a proposed edge selector `Γ(q) = -log Z_q`).

## What is proved

**Part 1 (curvature from the metric, no shortcut).** For the spatially flat FLRW metric
`g = -dt² + a(t)² (dx²+dy²+dz²)` on `ℝ⁴` (indices `Fin 4`, coordinate derivatives realised by
`deriv` in `t`), the Christoffel symbols and Ricci tensor are *defined* by the usual formulas
from `g` and `g⁻¹` and then *computed* (`Γ_eq`, `Ric_eq`, `Rs_eq`):
`R_00 = -3ä/a`, `R_ij = (aä + 2ȧ²) δ_ij`, others `0`, `R = 6(ä/a + ȧ²/a²)`.
Hypotheses: `a > 0`, `a` and `ȧ` differentiable. For `a = exp(Ht)`, `Ric = 3H² g` and the
trace-free part `Ric - R g/4` vanishes for every `H` (`dS_Ric`, `dS_traceFree`).
`traceFree_dS_family`: for every radius `ℓ > 0` de Sitter solves the vacuum trace-free
equations, and `ℓ ↦ Λ_eff = 3/ℓ²` is injective: a continuum of distinct Λ solves the same
local equations.

**Part 2 (integration constant).** With the full trace-free equations for a perfect fluid and
the continuity equation (`∇^μ T_{μν} = 0` in FLRW form), `d/dt (R + 8πG T) = 0`, so
`R + 8πG T = 4Λ` for a constant Λ and the Friedmann equation `3(ȧ/a)² = 8πGρ + Λ` holds
(`integration_constant`). Every `Λ ≥ 0` is realised by the vacuum de Sitter / Minkowski
solution with `H = √(Λ/3)` (`integration_constant_realised`). (Negative Λ with matter is not
constructed here.)

**Part 3 (selector calculus on ℕ).**
* `selector_exists_min`: any coercive `Γ : ℕ → ℝ` attains its minimum (convexity is not
  even needed).
* `minimisers_ordConnected`: under discrete convexity the minimiser set is an interval;
  (when convexity is not strict, flat bottoms of any length can occur; this example is
  not formalised here).
* `strict_minimisers_adjacent`: under strict discrete convexity there are at most two
  minimisers, and they are adjacent; `strict_tie_example` shows that a tie really can occur,
  so strict convexity alone does NOT give uniqueness. `strict_unique_of_no_tie`: uniqueness
  holds when, in addition, no increment vanishes (the sign-change condition of 2026-08-17).
* `selector_nogo`, `lambda_not_determined_by_structure`: for every `q*` the selector
  `(q - q*)²` is strictly convex, coercive, with unique minimiser `q*`; distinct `q*` give
  distinct `Λ = 3π/(ℓ_P² q*)`. Convexity + coercivity therefore select nothing.
* `affine_reweighting_moves_minimiser`: the affine reweighting `Z_q ↦ C e^{aq} Z_q`, which
  2026-08-17 itself identifies as scheme freedom leaving its "complete invariant"
  `κ_q = Δ² log I_q` unchanged, moves the unique minimiser of any strictly convex selector
  with unbounded increments to ANY prescribed `q*`, keeping strict convexity and coercivity.
* `poisson_selector_any_target`: for the explicit amplitude `Z_q = ζ^q/q!` (the 2026-08-17
  form `I_q/Γ(q+1)` with `I_q = ζ^q`), every `q*` is the unique minimiser for some `ζ > 0`.
* `gammaEdge_unique_min`, `qEdge_any_target`: the leading 2026-08-12 edge free energy
  `x (log(x/q_edge) - 1)` has unique minimiser `x = q_edge`, and
  `q_edge = Ξ exp(16π²/(b g²))` hits every value `> Ξ` for exactly one `b g² > 0`.
  So the minimiser is exactly the input parameter `b g²` (equivalently `q_edge`).
* `shell_any_integer`: the Fibonacci shell `n(q) = log_φ √(q/π)` takes every integer `N` at
  `q = π φ^{2N}`; the shell label `N_φ = 292` is a relabelling of the capacity input.

**Part 4.** A vacuum-energy shift `T_{μν} → T_{μν} - δ g_{μν}` drops out of the trace-free
equations (`TFEq_vacuum_shift`); the trace-free part of `δ g` is zero, in the FLRW model and
for any invertible 4×4 matrix (`traceFree_of_metric_shift`, `..._matrix`).

## Scope (read this)

* This shows that the **local** trace-free mechanism does **not** determine Λ: Λ is an
  integration constant, every non-negative value occurs, and structural properties of a
  selector (convexity, coercivity, affine-invariant curvature) do not determine `q*`.
* It does **not** refute global or microscopic selection mechanisms: a concrete `Z_q` with
  all parameters derived from first principles is untouched by these results; such a
  derivation is exactly the additional input that is required.
* No claim whatsoever is made about the observed value of Λ.
* The FLRW curvature is computed from the metric only for metrics depending on `t` alone
  (`∂_i ≡ 0` is built into `pd`); this is not a general Riemannian-geometry library.
-/

open Finset Filter

namespace APEX.Cosmology.Lambda

/-! ## Part 1: FLRW curvature computed from the metric -/

/-- Coordinate partial derivative `∂_m` of a field that depends only on `t = x⁰`:
`∂_0 f = f'`, `∂_i f = 0` for the spatial directions `i = 1,2,3`. -/
noncomputable def pd (m : Fin 4) (f : ℝ → ℝ) (t : ℝ) : ℝ := if m = 0 then deriv f t else 0

/-- Spatially flat FLRW metric `g = -dt² + a(t)² (dx² + dy² + dz²)`, indices in `Fin 4`. -/
def g (a : ℝ → ℝ) (μ ν : Fin 4) (t : ℝ) : ℝ :=
  if μ = ν then (if μ = 0 then -1 else a t ^ 2) else 0

/-- Inverse metric `g^{μν} = diag(-1, a⁻², a⁻², a⁻²)`. -/
noncomputable def ginv (a : ℝ → ℝ) (μ ν : Fin 4) (t : ℝ) : ℝ :=
  if μ = ν then (if μ = 0 then -1 else 1 / a t ^ 2) else 0

/-- Christoffel symbols computed from the metric:
`Γ^l_{mn} = ½ g^{ls} (∂_m g_{sn} + ∂_n g_{sm} - ∂_s g_{mn})`. -/
noncomputable def Γ (a : ℝ → ℝ) (l m n : Fin 4) (t : ℝ) : ℝ :=
  ∑ s, (1/2 : ℝ) * ginv a l s t * (pd m (g a s n) t + pd n (g a s m) t - pd s (g a m n) t)

/-- The expected closed form: `Γ^0_{ij} = a ȧ δ_ij`, `Γ^i_{0j} = Γ^i_{j0} = (ȧ/a) δ^i_j`,
all others zero. -/
noncomputable def Γc (a : ℝ → ℝ) (l m n : Fin 4) (t : ℝ) : ℝ :=
  if l = 0 then (if m = n ∧ m ≠ 0 then a t * deriv a t else 0)
  else (if (m = 0 ∧ n = l) ∨ (n = 0 ∧ m = l) then deriv a t / a t else 0)

lemma deriv_g (a : ℝ → ℝ) (hd : Differentiable ℝ a) (s n : Fin 4) (t : ℝ) :
    deriv (g a s n) t = if s = n ∧ s ≠ 0 then 2 * a t * deriv a t else 0 := by
  by_cases h1 : s = n
  · subst h1
    by_cases h2 : s = 0
    · have : g a s s = fun _ => -1 := by funext t; simp [g, h2]
      rw [this]; simp [h2]
    · have : g a s s = fun t => a t ^ 2 := by funext t; simp [g, h2]
      rw [this, deriv_fun_pow (hd t) 2]
      simp [h2]
  · have : g a s n = fun _ => 0 := by funext t; simp [g, h1]
    rw [this]; simp [h1]

lemma pd_g (a : ℝ → ℝ) (hd : Differentiable ℝ a) (m s n : Fin 4) (t : ℝ) :
    pd m (g a s n) t = if m = 0 ∧ s = n ∧ s ≠ 0 then 2 * a t * deriv a t else 0 := by
  unfold pd; rw [deriv_g a hd]
  by_cases hm : m = 0 <;> simp [hm]

/-- The Christoffel symbols computed from the metric agree with the closed form. -/
lemma Γ_eq (a : ℝ → ℝ) (ha : ∀ t, 0 < a t) (hd : Differentiable ℝ a) (l m n : Fin 4) :
    Γ a l m n = Γc a l m n := by
  funext t
  have hat := (ha t).ne'
  unfold Γ Γc
  simp only [pd_g a hd, ginv, Fin.sum_univ_four]
  fin_cases l <;> fin_cases m <;> fin_cases n <;> simp <;> field_simp


lemma deriv_Γc (a : ℝ → ℝ) (ha : ∀ t, 0 < a t) (hd : Differentiable ℝ a)
    (hd2 : Differentiable ℝ (deriv a)) (l m n : Fin 4) (t : ℝ) :
    deriv (Γc a l m n) t =
      if l = 0 then (if m = n ∧ m ≠ 0 then deriv a t ^ 2 + a t * deriv (deriv a) t else 0)
      else (if (m = 0 ∧ n = l) ∨ (n = 0 ∧ m = l) then
        (deriv (deriv a) t * a t - deriv a t ^ 2) / a t ^ 2 else 0) := by
  have hat := (ha t).ne'
  by_cases hl : l = 0
  · by_cases hc : m = n ∧ m ≠ 0
    · have : Γc a l m n = fun t => a t * deriv a t := by
        funext t; unfold Γc; rw [if_pos hl, if_pos hc]
      rw [this, deriv_fun_mul (hd t) (hd2 t),
        if_pos hl, if_pos hc]; ring
    · have : Γc a l m n = fun _ => 0 := by funext t; unfold Γc; rw [if_pos hl, if_neg hc]
      rw [this, if_pos hl, if_neg hc]; simp
  · by_cases hc : (m = 0 ∧ n = l) ∨ (n = 0 ∧ m = l)
    · have : Γc a l m n = fun t => deriv a t / a t := by
        funext t; unfold Γc; rw [if_neg hl, if_pos hc]
      rw [this, deriv_fun_div (hd2 t) (hd t) hat,
        if_neg hl, if_pos hc]; ring
    · have : Γc a l m n = fun _ => 0 := by funext t; unfold Γc; rw [if_neg hl, if_neg hc]
      rw [this, if_neg hl, if_neg hc]; simp

/-- Ricci tensor computed from the Christoffel symbols:
`R_{mn} = ∂_l Γ^l_{mn} - ∂_n Γ^l_{ml} + Γ^l_{ls} Γ^s_{mn} - Γ^l_{ns} Γ^s_{ml}`. -/
noncomputable def Ric (a : ℝ → ℝ) (m n : Fin 4) (t : ℝ) : ℝ :=
  ∑ l, pd l (Γ a l m n) t - ∑ l, pd n (Γ a l m l) t
    + ∑ l, ∑ s, (Γ a l l s t * Γ a s m n t - Γ a l n s t * Γ a s m l t)

/-- **FLRW Ricci tensor, computed from the metric.** For a positive scale factor `a` with
`a` and `ȧ` differentiable: `R_00 = -3 ä/a`, `R_ij = (a ä + 2 ȧ²) δ_ij`, all mixed components
zero. -/
theorem Ric_eq (a : ℝ → ℝ) (ha : ∀ t, 0 < a t) (hd : Differentiable ℝ a)
    (hd2 : Differentiable ℝ (deriv a)) (m n : Fin 4) (t : ℝ) :
    Ric a m n t = if m = n then
      (if m = 0 then -3 * deriv (deriv a) t / a t
       else a t * deriv (deriv a) t + 2 * deriv a t ^ 2) else 0 := by
  have hat := (ha t).ne'
  unfold Ric
  simp only [Γ_eq a ha hd, pd, deriv_Γc a ha hd hd2, Fin.sum_univ_four]
  fin_cases m <;> fin_cases n <;> simp [Γc] <;> field_simp <;> ring


/-- Scalar curvature `R = g^{μν} R_{μν}`. -/
noncomputable def Rs (a : ℝ → ℝ) (t : ℝ) : ℝ := ∑ m, ∑ n, ginv a m n t * Ric a m n t

/-- **FLRW scalar curvature** `R = 6 (ä/a + ȧ²/a²)`. -/
theorem Rs_eq (a : ℝ → ℝ) (ha : ∀ t, 0 < a t) (hd : Differentiable ℝ a)
    (hd2 : Differentiable ℝ (deriv a)) (t : ℝ) :
    Rs a t = 6 * (deriv (deriv a) t / a t + deriv a t ^ 2 / a t ^ 2) := by
  have hat := (ha t).ne'
  unfold Rs
  simp only [Ric_eq a ha hd hd2, ginv, Fin.sum_univ_four]
  simp
  field_simp
  ring

/-- Trace-free part of the Ricci tensor, `Ric - (1/4) R g`. -/
noncomputable def TF (a : ℝ → ℝ) (m n : Fin 4) (t : ℝ) : ℝ := Ric a m n t - Rs a t / 4 * g a m n t

/-- de Sitter scale factor `a(t) = exp(H t)` (radius `ℓ = 1/H`). -/
noncomputable def dS (H : ℝ) (t : ℝ) : ℝ := Real.exp (H * t)

lemma dS_pos (H t : ℝ) : 0 < dS H t := Real.exp_pos _

lemma hasDerivAt_dS (H t : ℝ) : HasDerivAt (dS H) (H * dS H t) t := by
  have := ((hasDerivAt_id t).const_mul H).exp
  simp only [id_eq, mul_one] at this
  unfold dS; rw [mul_comm]; exact this

lemma deriv_dS (H : ℝ) : deriv (dS H) = fun t => H * dS H t :=
  funext fun t => (hasDerivAt_dS H t).deriv

lemma differentiable_dS (H : ℝ) : Differentiable ℝ (dS H) :=
  fun t => (hasDerivAt_dS H t).differentiableAt

lemma differentiable_deriv_dS (H : ℝ) : Differentiable ℝ (deriv (dS H)) := by
  rw [deriv_dS]; exact (differentiable_dS H).const_mul H

lemma deriv2_dS (H t : ℝ) : deriv (deriv (dS H)) t = H ^ 2 * dS H t := by
  rw [deriv_dS, ((hasDerivAt_dS H t).const_mul H).deriv]; ring

/-- de Sitter is an Einstein space: `Ric = 3 H² g`. -/
theorem dS_Ric (H : ℝ) (m n : Fin 4) (t : ℝ) :
    Ric (dS H) m n t = 3 * H ^ 2 * g (dS H) m n t := by
  have hat := (dS_pos H t).ne'
  rw [Ric_eq _ (dS_pos H) (differentiable_dS H) (differentiable_deriv_dS H), deriv2_dS, deriv_dS]
  unfold g
  by_cases h1 : m = n
  · subst h1
    by_cases h2 : m = 0
    · simp only [h2, if_true]; field_simp
    · simp only [h2, if_true, if_false]; ring
  · simp [h1]

theorem dS_Rs (H t : ℝ) : Rs (dS H) t = 12 * H ^ 2 := by
  have hat := (dS_pos H t).ne'
  rw [Rs_eq _ (dS_pos H) (differentiable_dS H) (differentiable_deriv_dS H), deriv2_dS, deriv_dS]
  field_simp; ring

theorem dS_traceFree (H : ℝ) (m n : Fin 4) (t : ℝ) : TF (dS H) m n t = 0 := by
  unfold TF; rw [dS_Ric, dS_Rs]; ring

/-- Effective cosmological constant of de Sitter of radius `ℓ`. -/
noncomputable def LambdaEff (ℓ : ℝ) : ℝ := 3 / ℓ ^ 2

/-- **Main theorem (Part 1).** For every radius `ℓ > 0`, de Sitter space of radius `ℓ`
(scale factor `exp(t/ℓ)`) solves the vacuum trace-free Einstein equations
`Ric - (1/4) R g = 0`, and is an Einstein space with `Ric = Λ_eff(ℓ) g`, `Λ_eff = 3/ℓ²`.
The map `ℓ ↦ Λ_eff(ℓ)` is injective on `ℓ > 0`: a continuum of distinct effective
cosmological constants satisfies the same local trace-free equations. -/
theorem traceFree_dS_family :
    (∀ ℓ : ℝ, 0 < ℓ → (∀ m n t, TF (dS (1 / ℓ)) m n t = 0) ∧
        (∀ m n t, Ric (dS (1 / ℓ)) m n t = LambdaEff ℓ * g (dS (1 / ℓ)) m n t)) ∧
    Set.InjOn LambdaEff (Set.Ioi 0) := by
  refine ⟨fun ℓ hℓ => ⟨fun m n t => dS_traceFree _ m n t, fun m n t => ?_⟩, ?_⟩
  · rw [dS_Ric]; unfold LambdaEff; field_simp
  · intro x hx y hy hxy
    simp only [Set.mem_Ioi] at hx hy
    unfold LambdaEff at hxy
    have hx2 : x ^ 2 ≠ 0 := by positivity
    have hy2 : y ^ 2 ≠ 0 := by positivity
    field_simp at hxy
    have : (y - x) * (y + x) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith

/-! ## Part 2: the integration constant -/

/-- Perfect-fluid stress tensor `T_{μν} = diag(ρ, p a², p a², p a²)` in the FLRW frame. -/
noncomputable def Tm (a ρ p : ℝ → ℝ) (m n : Fin 4) (t : ℝ) : ℝ :=
  if m = n then (if m = 0 then ρ t else p t * a t ^ 2) else 0

/-- Trace `T = g^{μν} T_{μν}`. -/
noncomputable def Ttr (a ρ p : ℝ → ℝ) (t : ℝ) : ℝ := ∑ m, ∑ n, ginv a m n t * Tm a ρ p m n t

lemma Ttr_eq (a ρ p : ℝ → ℝ) (ha : ∀ t, 0 < a t) (t : ℝ) : Ttr a ρ p t = -ρ t + 3 * p t := by
  have hat := (ha t).ne'
  unfold Ttr; simp [Tm, ginv, Fin.sum_univ_four]; field_simp; ring

/-- The trace-free Einstein equations `Ric - R g/4 = 8πG (T - T g/4)` (all 16 components)
for the FLRW metric with scale factor `a` and perfect fluid `(ρ, p)`. -/
def TFEq (a : ℝ → ℝ) (G : ℝ) (ρ p : ℝ → ℝ) : Prop :=
  ∀ m n t, TF a m n t = 8 * Real.pi * G * (Tm a ρ p m n t - Ttr a ρ p t / 4 * g a m n t)

/-- The `00` trace-free equation is the Raychaudhuri combination `Ḣ = -4πG(ρ+p)`. -/
lemma TFEq_raychaudhuri {a : ℝ → ℝ} {G : ℝ} {ρ p : ℝ → ℝ} (ha : ∀ t, 0 < a t)
    (hd : Differentiable ℝ a) (hd2 : Differentiable ℝ (deriv a)) (h : TFEq a G ρ p) (t : ℝ) :
    deriv (deriv a) t / a t - (deriv a t / a t) ^ 2 = -(4 * Real.pi * G * (ρ t + p t)) := by
  have hat := (ha t).ne'
  have h0 := h 0 0 t
  unfold TF at h0
  rw [Ric_eq a ha hd hd2, Rs_eq a ha hd hd2, Ttr_eq a ρ p ha] at h0
  simp [g, Tm] at h0
  have e : deriv a t ^ 2 / a t ^ 2 = (deriv a t / a t) ^ 2 := by rw [div_pow]
  rw [e] at h0
  have e2 : -(3 * deriv (deriv a) t) / a t = -3 * (deriv (deriv a) t / a t) := by ring
  rw [e2] at h0
  linear_combination (-2/3 : ℝ) * h0

/-- **Main theorem (Part 2).** Trace-free equations plus matter conservation
(continuity equation `ρ̇ + 3 (ȧ/a)(ρ + p) = 0`, i.e. `∇^μ T_{μν} = 0` in FLRW form):
the quantity `R + 8πG T` has zero time derivative, it is therefore a constant `4Λ`, and the
full Friedmann equation with that integration constant, `3 (ȧ/a)² = 8πG ρ + Λ`, holds.
(The contracted Bianchi identity of the geometric side is built in, since the curvature is
computed explicitly from the metric.) -/
theorem integration_constant {a : ℝ → ℝ} {G : ℝ} {ρ p : ℝ → ℝ} (ha : ∀ t, 0 < a t)
    (hd : Differentiable ℝ a) (hd2 : Differentiable ℝ (deriv a)) (hρ : Differentiable ℝ ρ)
    (hcont : ∀ t, deriv ρ t + 3 * (deriv a t / a t) * (ρ t + p t) = 0)
    (h : TFEq a G ρ p) :
    (∀ t, deriv (fun s => Rs a s + 8 * Real.pi * G * Ttr a ρ p s) t = 0) ∧
    ∃ Λ : ℝ, ∀ t, Rs a t + 8 * Real.pi * G * Ttr a ρ p t = 4 * Λ ∧
      3 * (deriv a t / a t) ^ 2 = 8 * Real.pi * G * ρ t + Λ := by
  set F : ℝ → ℝ := fun s => 4 * (3 * (deriv a s / a s) ^ 2 - 8 * Real.pi * G * ρ s) with hF
  have hEq : (fun s => Rs a s + 8 * Real.pi * G * Ttr a ρ p s) = F := by
    funext s
    have hat := (ha s).ne'
    have hr := TFEq_raychaudhuri ha hd hd2 h s
    rw [Rs_eq a ha hd hd2, Ttr_eq a ρ p ha, hF]
    have e : deriv a s ^ 2 / a s ^ 2 = (deriv a s / a s) ^ 2 := by rw [div_pow]
    rw [e]
    linarith
  have hFd : ∀ t, HasDerivAt F 0 t := by
    intro t
    have hat := (ha t).ne'
    have h1 := (hd2 t).hasDerivAt.div (hd t).hasDerivAt hat
    have h2 := (((h1.pow 2).const_mul 3).sub ((hρ t).hasDerivAt.const_mul (8 * Real.pi * G))).const_mul 4
    convert h2 using 1
    have hr := TFEq_raychaudhuri ha hd hd2 h t
    have e1 : (deriv (deriv a) t * a t - deriv a t * deriv (a) t) / a t ^ 2
        = -(4 * Real.pi * G * (ρ t + p t)) := by
      rw [← hr]; field_simp
    have e2 : deriv ρ t = -(3 * (deriv a t / a t) * (ρ t + p t)) := by linarith [hcont t]
    simp only [Nat.cast_ofNat, Pi.div_apply]
    rw [e1, e2]; ring
  refine ⟨fun t => by rw [hEq]; exact (hFd t).deriv, ?_⟩
  have hdiff : Differentiable ℝ F := fun t => (hFd t).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun t => (hFd t).deriv)
  refine ⟨F 0 / 4, fun t => ⟨?_, ?_⟩⟩
  · have h3 : Rs a t + 8 * Real.pi * G * Ttr a ρ p t = F t := congrFun hEq t
    rw [h3, hconst t 0]; ring
  · have h3 : F t = F 0 := hconst t 0
    simp only [hF] at h3
    linarith

/-- **Every constant `Λ ≥ 0` is realised (vacuum).** For every `Λ ≥ 0` the de Sitter
(Minkowski for `Λ = 0`) solution with `H = √(Λ/3)` solves the vacuum trace-free equations,
trivially satisfies the continuity equation, and has `R + 8πG T = 4Λ`. -/
theorem integration_constant_realised (G Λ : ℝ) (hΛ : 0 ≤ Λ) :
    let a := dS (Real.sqrt (Λ / 3))
    TFEq a G (fun _ => 0) (fun _ => 0) ∧
    (∀ t, deriv (fun _ : ℝ => (0:ℝ)) t + 3 * (deriv a t / a t) * (0 + 0) = 0) ∧
    (∀ t, Rs a t + 8 * Real.pi * G * Ttr a (fun _ => 0) (fun _ => 0) t = 4 * Λ) := by
  intro a
  have hs : Real.sqrt (Λ / 3) ^ 2 = Λ / 3 := Real.sq_sqrt (by linarith)
  refine ⟨fun m n t => ?_, fun t => by simp, fun t => ?_⟩
  · rw [dS_traceFree]; simp [Tm, Ttr]
  · rw [dS_Rs, Ttr_eq _ _ _ (dS_pos _), hs]; ring

/-! ## Part 3: abstract selector calculus on `ℕ` -/

/-- Forward increment `ΔΓ(q) = Γ(q+1) - Γ(q)`. -/
def incr (G : ℕ → ℝ) (q : ℕ) : ℝ := G (q+1) - G q

def DiscreteConvex (G : ℕ → ℝ) : Prop := ∀ q, incr G q ≤ incr G (q+1)
def StrictDiscreteConvex (G : ℕ → ℝ) : Prop := ∀ q, incr G q < incr G (q+1)
def Coercive (G : ℕ → ℝ) : Prop := Tendsto G atTop atTop
def IsMinimiser (G : ℕ → ℝ) (q : ℕ) : Prop := ∀ n, G q ≤ G n

lemma incr_mono {G : ℕ → ℝ} (h : DiscreteConvex G) : Monotone (incr G) :=
  monotone_nat_of_le_succ h

lemma incr_strictMono {G : ℕ → ℝ} (h : StrictDiscreteConvex G) : StrictMono (incr G) :=
  strictMono_nat_of_lt_succ h

/-- lower bound: G (j+n) - G j ≥ n * incr G j -/
lemma lower_bound {G : ℕ → ℝ} (h : DiscreteConvex G) (j n : ℕ) :
    (n : ℝ) * incr G j ≤ G (j+n) - G j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : incr G j ≤ incr G (j+n) := incr_mono h (by omega)
    have : G (j + (n+1)) = G (j+n) + incr G (j+n) := by
      simp [incr, ← add_assoc]
    push_cast; rw [this]; nlinarith

/-- upper bound: G (j+n+1) - G j ≤ (n+1) * incr G (j+n) -/
lemma upper_bound {G : ℕ → ℝ} (h : DiscreteConvex G) (j n : ℕ) :
    G (j+n+1) - G j ≤ ((n:ℝ)+1) * incr G (j+n) := by
  induction n with
  | zero => simp [incr]
  | succ n ih =>
    have hm : incr G (j+n) ≤ incr G (j+(n+1)) := incr_mono h (by omega)
    have : G (j + (n+1) + 1) = G (j+n+1) + incr G (j+(n+1)) := by
      simp [incr, ← add_assoc]
    push_cast; rw [this]; nlinarith

theorem selector_exists_min (G : ℕ → ℝ) (hc : Coercive G) : ∃ q, IsMinimiser G q := by
  obtain ⟨N, hN⟩ := (hc.eventually_gt_atTop (G 0)).exists_forall_of_atTop
  obtain ⟨q, -, hq⟩ := (Finset.range (N+1)).exists_min_image G ⟨0, by simp⟩
  refine ⟨q, fun n => ?_⟩
  by_cases hn : n < N + 1
  · exact hq n (Finset.mem_range.2 hn)
  · have h0 := hq 0 (by simp)
    have := hN n (by omega); linarith

theorem minimisers_ordConnected {G : ℕ → ℝ} (h : DiscreteConvex G) {q₁ q q₂ : ℕ}
    (h1 : IsMinimiser G q₁) (h2 : IsMinimiser G q₂) (hq1 : q₁ ≤ q) (hq2 : q ≤ q₂) :
    IsMinimiser G q := by
  intro n
  rcases Nat.eq_or_lt_of_le hq1 with rfl | hlt
  · exact h1 n
  by_contra hcon
  push Not at hcon
  have hgt : G q₁ < G q := lt_of_le_of_lt (h1 n) hcon
  obtain ⟨k, rfl⟩ : ∃ k, q = q₁ + k + 1 := ⟨q - q₁ - 1, by omega⟩
  have hu := upper_bound h q₁ k
  have hpos : 0 < incr G (q₁ + k) := by
    by_contra hneg; push Not at hneg
    have : ((k:ℝ)+1) * incr G (q₁+k) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  obtain ⟨m, hm⟩ : ∃ m, q₂ = (q₁ + k + 1) + m := ⟨q₂ - (q₁+k+1), by omega⟩
  have hl := lower_bound h (q₁+k+1) m
  have hmono : incr G (q₁ + k) ≤ incr G (q₁+k+1) := incr_mono h (by omega)
  have : 0 ≤ (m:ℝ) * incr G (q₁+k+1) := mul_nonneg (by positivity) (by linarith)
  have := h2 q₁
  rw [hm] at this
  linarith

theorem strict_minimisers_adjacent {G : ℕ → ℝ} (h : StrictDiscreteConvex G) {q₁ q₂ : ℕ}
    (h1 : IsMinimiser G q₁) (h2 : IsMinimiser G q₂) (hle : q₁ ≤ q₂) : q₂ ≤ q₁ + 1 := by
  by_contra hc; push Not at hc
  have hc' : DiscreteConvex G := fun q => (h q).le
  have h0 : 0 ≤ incr G q₁ := by have := h1 (q₁+1); simp [incr]; linarith
  have hs : incr G q₁ < incr G (q₁+1) := h q₁
  obtain ⟨m, hm⟩ : ∃ m, q₂ = (q₁ + 1) + (m+1) := ⟨q₂ - q₁ - 2, by omega⟩
  have hl := lower_bound hc' (q₁+1) (m+1)
  have : 0 < ((m:ℝ)+1) * incr G (q₁+1) := mul_pos (by positivity) (by linarith)
  have h3 := h2 (q₁+1)
  rw [hm] at h3; push_cast at hl; linarith

theorem strict_unique_of_no_tie {G : ℕ → ℝ} (h : StrictDiscreteConvex G)
    (hnt : ∀ q, incr G q ≠ 0) {q₁ q₂ : ℕ}
    (h1 : IsMinimiser G q₁) (h2 : IsMinimiser G q₂) : q₁ = q₂ := by
  wlog hle : q₁ ≤ q₂ generalizing q₁ q₂
  · exact (this h2 h1 (by omega)).symm
  have := strict_minimisers_adjacent h h1 h2 hle
  rcases Nat.eq_or_lt_of_le hle with e | lt
  · exact e
  · exfalso
    have e2 : q₂ = q₁ + 1 := by omega
    subst e2
    have a := h1 (q₁+1); have b := h2 q₁
    exact hnt q₁ (by simp [incr]; linarith)

/-- example: strict convexity does not force uniqueness (tie at 0 and 1). -/
theorem strict_tie_example :
    StrictDiscreteConvex (fun q : ℕ => ((2:ℝ) * q - 1)^2) ∧
    IsMinimiser (fun q : ℕ => ((2:ℝ) * q - 1)^2) 0 ∧
    IsMinimiser (fun q : ℕ => ((2:ℝ) * q - 1)^2) 1 := by
  refine ⟨fun q => by simp [incr]; push_cast; nlinarith, fun n => ?_, fun n => ?_⟩ <;>
  · simp only; push_cast
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have : (1:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith


/-- **Part 3(b), no-go.** For every target `q*` the selector `Γ(q) = (q - q*)²` is strictly
discretely convex, coercive and has `q*` as its unique minimiser. -/
theorem selector_nogo (qs : ℕ) :
    let G : ℕ → ℝ := fun q => ((q : ℝ) - qs) ^ 2
    StrictDiscreteConvex G ∧ Coercive G ∧ IsMinimiser G qs ∧ ∀ q, IsMinimiser G q → q = qs := by
  intro G
  refine ⟨fun q => by simp [G, incr]; push_cast; nlinarith, ?_, fun n => by simp [G]; positivity, ?_⟩
  · unfold Coercive
    refine Filter.tendsto_atTop_atTop.2 fun b => ⟨qs + ⌈b⌉₊ + 1, fun q hq => ?_⟩
    have h1 : (qs : ℝ) + ⌈b⌉₊ + 1 ≤ q := by exact_mod_cast hq
    have h2 : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    have h3 : (0:ℝ) ≤ ⌈b⌉₊ := by positivity
    simp only [G]; nlinarith
  · intro q hq
    have := hq qs
    simp [G] at this
    exact_mod_cast (sub_eq_zero.1 this)

/-- Capacity map `q ↦ Λ_q = 3π/(ℓ_P² q)`. -/
noncomputable def LambdaCap (ℓP : ℝ) (q : ℕ) : ℝ := 3 * Real.pi / (ℓP ^ 2 * q)

lemma LambdaCap_injective (ℓP : ℝ) (hℓ : ℓP ≠ 0) {q₁ q₂ : ℕ} (h1 : 1 ≤ q₁) (h2 : 1 ≤ q₂)
    (h : LambdaCap ℓP q₁ = LambdaCap ℓP q₂) : q₁ = q₂ := by
  unfold LambdaCap at h
  have hq1 : (q₁ : ℝ) ≠ 0 := by positivity
  have hq2 : (q₂ : ℝ) ≠ 0 := by positivity
  have hπ := Real.pi_pos
  have hl : ℓP ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  rw [div_eq_div_iff (mul_ne_zero hl hq1) (mul_ne_zero hl hq2)] at h
  have h' : (3 * Real.pi * ℓP ^ 2) * (q₂ : ℝ) = (3 * Real.pi * ℓP ^ 2) * q₁ := by linarith
  have := mul_left_cancel₀ (by positivity : (3 * Real.pi * ℓP ^ 2) ≠ 0) h'
  exact_mod_cast this.symm

/-- **Part 3(b), consequence for Λ.** Every capacity value `Λ = 3π/(ℓ_P² q*)`, `q* ≥ 1`,
is the output of some strictly convex coercive selector with unique minimiser `q*`, and
different targets give different Λ. Convexity + coercivity do not determine Λ. -/
theorem lambda_not_determined_by_structure (ℓP : ℝ) (hℓ : ℓP ≠ 0) :
    (∀ qs : ℕ, ∃ G : ℕ → ℝ, StrictDiscreteConvex G ∧ Coercive G ∧
        IsMinimiser G qs ∧ ∀ q, IsMinimiser G q → q = qs) ∧
    (∀ q₁ q₂ : ℕ, 1 ≤ q₁ → 1 ≤ q₂ → q₁ ≠ q₂ → LambdaCap ℓP q₁ ≠ LambdaCap ℓP q₂) :=
  ⟨fun qs => ⟨_, selector_nogo qs⟩,
   fun _ _ h1 h2 hne h => hne (LambdaCap_injective ℓP hℓ h1 h2 h)⟩

/-! ### Part 3(c): affine (boundary-tension) reweighting moves the minimiser -/

lemma unique_min_of_sign_change (F : ℕ → ℝ) (qs : ℕ)
    (hneg : ∀ q, q < qs → incr F q < 0) (hpos : ∀ q, qs ≤ q → 0 < incr F q) :
    ∀ n, n ≠ qs → F qs < F n := by
  have up : ∀ k, F qs < F (qs + k + 1) := by
    intro k; induction k with
    | zero => have := hpos qs le_rfl; simp [incr] at this; simpa using this
    | succ k ih =>
      have := hpos (qs + k + 1) (by omega); simp [incr] at this
      have e : qs + (k+1) + 1 = qs + k + 1 + 1 := by omega
      rw [e]; linarith
  have down : ∀ n, n < qs → ∀ k, n + k + 1 ≤ qs → F (n + k + 1) < F n := by
    intro n hn k; induction k with
    | zero => intro _; have := hneg n hn; simp [incr] at this; simpa using this
    | succ k ih =>
      intro hk
      have := hneg (n + k + 1) (by omega); simp [incr] at this
      have e : n + (k+1) + 1 = n + k + 1 + 1 := by omega
      rw [e]; linarith [ih (by omega)]
  intro n hn
  rcases Nat.lt_or_gt_of_ne hn with h | h
  · have := down n h (qs - n - 1) (by omega)
    have e : n + (qs - n - 1) + 1 = qs := by omega
    rwa [e] at this
  · have := up (n - qs - 1)
    have e : qs + (n - qs - 1) + 1 = n := by omega
    rwa [e] at this

lemma coercive_of_incr_ge_one (F : ℕ → ℝ) (N : ℕ) (h : ∀ q, N ≤ q → 1 ≤ incr F q) : Coercive F := by
  have lb : ∀ n, F N + n ≤ F (N + n) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      have := h (N + n) (by omega); simp [incr] at this
      have e : N + (n+1) = N + n + 1 := by omega
      rw [e]; push_cast; linarith
  unfold Coercive
  refine Filter.tendsto_atTop_atTop.2 fun b => ⟨N + ⌈b - F N⌉₊, fun q hq => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = N + n := ⟨q - N, by omega⟩
  have h1 : (⌈b - F N⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈b - F N⌉₊ ≤ n)
  have h2 := Nat.le_ceil (b - F N)
  linarith [lb n]

/-- **Part 3(c), affine-reweighting theorem.** Let `Γ` be strictly discretely convex with
unbounded increments. The affine (boundary-tension / normalisation) reweighting
`Z_q ↦ C e^{a q} Z_q` of the 2026-08-17 paper acts as `Γ ↦ Γ - a q - log C`. It leaves the
second differences (the paper's "complete selector invariant" κ_q) unchanged, keeps strict
convexity and coercivity, and for EVERY target `q*` there is an `a` making `q*` the unique
minimiser. -/
theorem affine_reweighting_moves_minimiser (G : ℕ → ℝ) (hG : StrictDiscreteConvex G)
    (hunb : Tendsto (incr G) atTop atTop) (qs : ℕ) :
    ∃ a : ℝ, let Ga : ℕ → ℝ := fun q => G q - a * q
      (∀ q, incr (incr Ga) q = incr (incr G) q) ∧
      StrictDiscreteConvex Ga ∧ Coercive Ga ∧
      IsMinimiser Ga qs ∧ ∀ q, IsMinimiser Ga q → q = qs := by
  have hsm := incr_strictMono hG
  let a : ℝ := if qs = 0 then incr G 0 - 1 else (incr G (qs - 1) + incr G qs) / 2
  have hinc : ∀ q, incr (fun q : ℕ => G q - a * q) q = incr G q - a := by
    intro q; simp [incr]; ring
  have hneg : ∀ q, q < qs → incr G q - a < 0 := by
    intro q hq
    have hq0 : qs ≠ 0 := by omega
    have h1 : incr G q ≤ incr G (qs - 1) := hsm.monotone (by omega)
    have h2 : incr G (qs - 1) < incr G qs := hsm (by omega)
    simp only [a, hq0, if_false]; linarith
  have hpos : ∀ q, qs ≤ q → 0 < incr G q - a := by
    intro q hq
    have h1 : incr G qs ≤ incr G q := hsm.monotone hq
    by_cases hq0 : qs = 0
    · simp only [a, hq0, if_true]; subst hq0
      have := hsm.monotone (Nat.zero_le q); linarith
    · have h2 : incr G (qs - 1) < incr G qs := hsm (by omega)
      simp only [a, hq0, if_false]; linarith
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; simp only [incr]; push_cast; ring
  · intro q; rw [hinc, hinc]; linarith [hG q]
  · obtain ⟨N, hN⟩ := (hunb.eventually_ge_atTop (a + 1)).exists_forall_of_atTop
    exact coercive_of_incr_ge_one _ N fun q hq => by rw [hinc]; linarith [hN q hq]
  · have hu := unique_min_of_sign_change (fun q : ℕ => G q - a * q) qs
      (fun q hq => by rw [hinc]; exact hneg q hq) (fun q hq => by rw [hinc]; exact hpos q hq)
    intro n; by_cases hn : n = qs
    · rw [hn]
    · exact (hu n hn).le
  · intro q hq
    by_contra hne
    have hu := unique_min_of_sign_change (fun q : ℕ => G q - a * q) qs
      (fun q hq => by rw [hinc]; exact hneg q hq) (fun q hq => by rw [hinc]; exact hpos q hq)
    have := hu q hne
    have := hq qs
    linarith

/-- The Poisson-type amplitude `Z_q = ζ^q / q!` (the 2026-08-17 form `Z_q = I_q/Γ(q+1)`
with `I_q = ζ^q`): `Γ_ζ(q) = -log Z_q = log q! - q log ζ`. -/
noncomputable def GammaPoisson (ζ : ℝ) (q : ℕ) : ℝ := Real.log (q.factorial : ℝ) - q * Real.log ζ

lemma incr_logFactorial (q : ℕ) :
    incr (fun q : ℕ => Real.log (q.factorial : ℝ)) q = Real.log ((q : ℝ) + 1) := by
  simp only [incr]
  rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  push_cast; ring

/-- **Part 3(c), explicit `Z_q`.** For the factorial amplitude `Z_q = ζ^q/q!`, the minimiser of
`Γ_ζ = -log Z_q` is set entirely by the free parameter `ζ > 0` (boundary fugacity / tension):
for every target `q*` there is `ζ > 0` making `q*` the unique minimiser. -/
theorem poisson_selector_any_target (qs : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ IsMinimiser (GammaPoisson ζ) qs ∧
      ∀ q, IsMinimiser (GammaPoisson ζ) q → q = qs := by
  have hG : StrictDiscreteConvex (fun q : ℕ => Real.log (q.factorial : ℝ)) := by
    intro q; rw [incr_logFactorial, incr_logFactorial]
    exact Real.log_lt_log (by positivity) (by push_cast; linarith)
  have hunb : Tendsto (incr (fun q : ℕ => Real.log (q.factorial : ℝ))) atTop atTop := by
    have : incr (fun q : ℕ => Real.log (q.factorial : ℝ)) = fun q : ℕ => Real.log ((q:ℝ) + 1) :=
      funext incr_logFactorial
    rw [this]
    exact Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨a, -, -, -, hmin, huniq⟩ := affine_reweighting_moves_minimiser _ hG hunb qs
  have e : GammaPoisson (Real.exp a) = fun q : ℕ => Real.log (q.factorial : ℝ) - a * q := by
    funext q; simp [GammaPoisson, Real.log_exp, mul_comm]
  exact ⟨Real.exp a, Real.exp_pos a, by rw [e]; exact hmin, by rw [e]; exact huniq⟩

/-! ### Part 3(c): the 2026-08-12 leading edge free energy -/

/-- Leading term of the 2026-08-12 edge free energy, `Γ(x) = x (log(x/c) - 1)`, `c = q_edge`. -/
noncomputable def GammaEdge (c x : ℝ) : ℝ := x * (Real.log (x / c) - 1)

/-- On `x > 0`, `GammaEdge c` has the unique minimiser `x = c`: its location is the input
parameter `c = q_edge` itself. -/
theorem gammaEdge_unique_min (c : ℝ) (hc : 0 < c) (x : ℝ) (hx : 0 < x) (hne : x ≠ c) :
    GammaEdge c c < GammaEdge c x := by
  unfold GammaEdge
  rw [div_self hc.ne', Real.log_one]
  have hy : 0 < c / x := div_pos hc hx
  have hy1 : c / x ≠ 1 := by
    intro h; apply hne; field_simp at h; linarith
  have hl := Real.log_lt_sub_one_of_pos hy hy1
  have e : Real.log (x / c) = - Real.log (c / x) := by
    rw [← Real.log_inv, inv_div]
  rw [e]
  have : x * (c / x - 1) = c - x := by field_simp
  nlinarith

/-- The edge centre `q_edge = Ξ exp(16π²/(b g²))` is a bijective function of the free
running parameter `b g² > 0` onto `(Ξ, ∞)`: every `c > Ξ` is reached by exactly one `b g²`. -/
theorem qEdge_any_target (Ξ c : ℝ) (hΞ : 0 < Ξ) (hc : Ξ < c) :
    ∃ bg : ℝ, 0 < bg ∧ Ξ * Real.exp (16 * Real.pi ^ 2 / bg) = c ∧
      ∀ bg' : ℝ, 0 < bg' → Ξ * Real.exp (16 * Real.pi ^ 2 / bg') = c → bg' = bg := by
  have hlog : 0 < Real.log (c / Ξ) := Real.log_pos (by rw [lt_div_iff₀ hΞ]; linarith)
  have hπ : 0 < 16 * Real.pi ^ 2 := by positivity
  refine ⟨16 * Real.pi ^ 2 / Real.log (c / Ξ), div_pos hπ hlog, ?_, ?_⟩
  · rw [div_div_cancel₀ hπ.ne', Real.exp_log (div_pos (by linarith) hΞ)]; field_simp
  · intro bg' hbg' h
    have h2 : Real.exp (16 * Real.pi ^ 2 / bg') = c / Ξ := by field_simp; linarith
    have h3 : 16 * Real.pi ^ 2 / bg' = Real.log (c / Ξ) := by rw [← h2, Real.log_exp]
    field_simp at h3 ⊢; linarith

/-- Golden ratio. -/
noncomputable def phiG : ℝ := (1 + Real.sqrt 5) / 2

lemma one_lt_phiG : 1 < phiG := by
  unfold phiG
  have : 1 < Real.sqrt 5 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- Fibonacci shell coordinate of 2026-08-12, `n(q) = log_φ √(q/π)`. -/
noncomputable def shell (q : ℝ) : ℝ := Real.log (Real.sqrt (q / Real.pi)) / Real.log phiG

/-- The shell label is only a reparametrisation of the capacity input: every integer `N` is the
exact shell of `q = π φ^{2N}`. (So `N_φ = 292` carries exactly the information of the
capacity value it was computed from.) -/
theorem shell_any_integer (N : ℕ) : shell (Real.pi * phiG ^ (2 * N)) = N := by
  unfold shell
  have hφ : 0 < phiG := by linarith [one_lt_phiG]
  have hl : Real.log phiG ≠ 0 := (Real.log_pos one_lt_phiG).ne'
  rw [mul_div_cancel_left₀ _ Real.pi_pos.ne', pow_mul', Real.sqrt_sq (by positivity), Real.log_pow]
  field_simp

/-! ## Part 4: vacuum-energy shifts drop out -/

/-- The trace-free part of `δ g` vanishes in the FLRW model. -/
theorem traceFree_of_metric_shift (a : ℝ → ℝ) (ha : ∀ t, 0 < a t) (δ : ℝ) (m n : Fin 4) (t : ℝ) :
    δ * g a m n t - (∑ μ, ∑ ν, ginv a μ ν t * (δ * g a μ ν t)) / 4 * g a m n t = 0 := by
  have hat := (ha t).ne'
  have : (∑ μ, ∑ ν, ginv a μ ν t * (δ * g a μ ν t)) = 4 * δ := by
    simp [ginv, g, Fin.sum_univ_four]; field_simp; ring
  rw [this]; ring

/-- Matrix version: for any invertible 4×4 metric, `δ g - (1/4) tr(g⁻¹ δ g) g = 0`. -/
theorem traceFree_of_metric_shift_matrix (g : Matrix (Fin 4) (Fin 4) ℝ) (hg : IsUnit g.det)
    (δ : ℝ) : δ • g - ((1 / 4 : ℝ) * Matrix.trace (g⁻¹ * (δ • g))) • g = 0 := by
  rw [Matrix.mul_smul, Matrix.nonsing_inv_mul g hg, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, smul_eq_mul]
  rw [← sub_smul]; convert zero_smul ℝ g; push_cast; ring

/-- **Radiative instability drops out.** Shifting the vacuum energy, `ρ → ρ + δ`,
`p → p - δ` (i.e. `T_{μν} → T_{μν} - δ g_{μν}`), leaves the trace-free equations unchanged. -/
theorem TFEq_vacuum_shift (a : ℝ → ℝ) (ha : ∀ t, 0 < a t) (G δ : ℝ) (ρ p : ℝ → ℝ) :
    TFEq a G (fun t => ρ t + δ) (fun t => p t - δ) ↔ TFEq a G ρ p := by
  have key : ∀ m n t, Tm a (fun t => ρ t + δ) (fun t => p t - δ) m n t
      - Ttr a (fun t => ρ t + δ) (fun t => p t - δ) t / 4 * g a m n t
      = Tm a ρ p m n t - Ttr a ρ p t / 4 * g a m n t := by
    intro m n t
    rw [Ttr_eq _ _ _ ha, Ttr_eq _ _ _ ha]
    unfold Tm g
    by_cases h1 : m = n
    · subst h1
      by_cases h2 : m = 0 <;> simp [h2] <;> ring
    · simp [h1]
  unfold TFEq
  simp only [key]

end APEX.Cosmology.Lambda

