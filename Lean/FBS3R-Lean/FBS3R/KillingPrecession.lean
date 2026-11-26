/-
# Killing precession does no work: shell energy law and exact decay

Source: *Killing–Beltrami algebra …*, Thm `thm:shellwiseprecession` (`D(m)* = -D(m)`),
Cor. `cor:highenergy` and Cor. "Closed unforced formula" (`‖v(t)‖ = e^{-νκ_k t}‖v₀‖`).

Abstract setting (any real inner-product space `E`, e.g. a shell `E_{k,σ}` with the `L²`
product): `v' = -c·v - D(t) v + F(t)` with every `D(t)` skew-adjoint.

Machine-checked:
* energy balance `d/dt ½‖v‖² = -c‖v‖² + ⟪F, v⟫` — the precession term drops out exactly;
* for `F = 0`: `‖v(t)‖ = e^{-c t} ‖v(0)‖` for all `t` (with `c = ν k(k+4)/R²` this is the
  paper's eq. `vdecay`).
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

namespace FBS3R.Precession

open Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- **Energy balance**: skew precession contributes no work. -/
theorem energy_balance (c : ℝ) (D : ℝ → E →ₗ[ℝ] E) (F v : ℝ → E)
    (hskew : ∀ t w, ⟪D t w, w⟫ = 0) (t : ℝ)
    (hv : HasDerivAt v (-c • v t - D t (v t) + F t) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖v s‖ ^ 2) (-c * ‖v t‖ ^ 2 + ⟪F t, v t⟫) t := by
  have h := (hv.norm_sq).const_mul (1 / 2 : ℝ)
  convert h using 1
  rw [inner_add_right, inner_sub_right, inner_smul_right, real_inner_comm (D t (v t)) (v t),
    hskew, real_inner_self_eq_norm_sq, real_inner_comm (F t) (v t)]
  ring

/-- **Exact decay** for the unforced shell equation `v' = -c v - D(t) v`. -/
theorem exact_decay (c : ℝ) (D : ℝ → E →ₗ[ℝ] E) (v : ℝ → E)
    (hskew : ∀ t w, ⟪D t w, w⟫ = 0)
    (hv : ∀ t, HasDerivAt v (-c • v t - D t (v t)) t) (t : ℝ) :
    ‖v t‖ = Real.exp (-c * t) * ‖v 0‖ := by
  -- g(s) = exp(2cs)‖v s‖² has zero derivative
  set g : ℝ → ℝ := fun s => Real.exp (2 * c * s) * ‖v s‖ ^ 2
  have hg : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (2 * c * s)) (Real.exp (2 * c * s) * (2 * c)) s := by
      have := ((hasDerivAt_id s).const_mul (2 * c)).exp
      simpa [mul_comm] using this
    have h2 := (hv s).norm_sq
    have := h1.mul h2
    convert this using 1
    rw [inner_sub_right, inner_smul_right, real_inner_comm (D s (v s)) (v s), hskew,
      real_inner_self_eq_norm_sq]
    ring
  have hconst : g t = g 0 := is_const_of_deriv_eq_zero
    (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  simp only [g, mul_zero, Real.exp_zero, one_mul] at hconst
  have e : Real.exp (-c * t) ^ 2 * Real.exp (2 * c * t) = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hsq : ‖v t‖ ^ 2 = (Real.exp (-c * t) * ‖v 0‖) ^ 2 := by
    calc ‖v t‖ ^ 2 = (Real.exp (-c * t) ^ 2 * Real.exp (2 * c * t)) * ‖v t‖ ^ 2 := by
          rw [e, one_mul]
      _ = Real.exp (-c * t) ^ 2 * (Real.exp (2 * c * t) * ‖v t‖ ^ 2) := by ring
      _ = (Real.exp (-c * t) * ‖v 0‖) ^ 2 := by rw [hconst]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end FBS3R.Precession
