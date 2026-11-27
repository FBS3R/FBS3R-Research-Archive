/-
# Lamb identity and the Beltrami mechanism behind exact Navier–Stokes reductions

Sources: *Killing–Beltrami algebra …*, Lemma "Polarized vector identity"
(`∇_u v + ∇_v u = grad⟨u,v⟩ - u × curl v - v × curl u`), whose diagonal case `u = v` is the
Lamb identity `(u·∇)u = ∇(|u|²/2) - u × curl u`.  On a Beltrami field (`curl u = λ u`)
the Lamb vector `u × curl u` vanishes, so the nonlinearity is a pure gradient and is
absorbed by the pressure: this is why every signed curl shell is an exact reducing space.

Machine-checked here (flat `ℝ³`, the local model of any oriented Riemannian 3-manifold):
* the **polarized identity** at the level of Jacobians (any `3×3` matrices `J, K`);
* the **Lamb identity for differentiable vector fields** `u : ℝ³ → ℝ³`
  (genuine Fréchet derivatives);
* **Beltrami ⇒ the advection term equals the gradient of `|u|²/2`.**
-/
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul

namespace FBS3R.Lamb

open Matrix

abbrev V3 := Fin 3 → ℝ

def cross (u v : V3) : V3 :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- curl from a Jacobian `J i j = ∂_j u_i`. -/
def curlJ (J : Matrix (Fin 3) (Fin 3) ℝ) : V3 := ![J 2 1 - J 1 2, J 0 2 - J 2 0, J 1 0 - J 0 1]

/-- **Polarized vector identity** at Jacobian level: with `J = Du`, `K = Dv`,
`K u + J v = (Kᵀ v + Jᵀ u)?` — precisely:
`(∇_u v + ∇_v u) = grad⟨u,v⟩ - u × curl v - v × curl u`, where
`∇_u v = K u`, `∇_v u = J v`, `grad⟨u,v⟩ = Jᵀ v + Kᵀ u`. -/
theorem polarized (J K : Matrix (Fin 3) (Fin 3) ℝ) (u v : V3) :
    K *ᵥ u + J *ᵥ v = (Jᵀ *ᵥ v + Kᵀ *ᵥ u) - cross u (curlJ K) - cross v (curlJ J) := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply]
  fin_cases i <;>
  · simp [mulVec, dotProduct, Fin.sum_univ_three, cross, curlJ, transpose_apply]; ring

/-- Lamb identity at Jacobian level: `J u = Jᵀ u - u × curl`. -/
theorem lamb_matrix (J : Matrix (Fin 3) (Fin 3) ℝ) (u : V3) :
    J *ᵥ u = Jᵀ *ᵥ u - cross u (curlJ J) := by
  funext i
  simp only [Pi.sub_apply]
  fin_cases i <;>
  · simp [mulVec, dotProduct, Fin.sum_univ_three, cross, curlJ, transpose_apply]; ring

lemma cross_smul_self (u : V3) (c : ℝ) : cross u (c • u) = 0 := by
  funext i; fin_cases i <;> · simp [cross]; ring

/-! ### Genuine vector fields -/

/-- Jacobian matrix of a linear map `ℝ³ → ℝ³`: `jac L i j = (L eⱼ)ᵢ`. -/
def jac (L : V3 →L[ℝ] V3) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => L (Pi.single j 1) i

lemma apply_eq_jac_mulVec (L : V3 →L[ℝ] V3) (w : V3) : L w = jac L *ᵥ w := by
  conv_lhs => rw [pi_eq_sum_univ w]
  funext i
  simp [map_sum, map_smul, mulVec, dotProduct, jac, mul_comm]
  congr 1; ext x
  rw [show (fun j => if x = j then (1:ℝ) else 0) = Pi.single x 1 from by
    ext j; simp [Pi.single_apply, eq_comm]]

/-- Derivative of the kinetic-energy density `e(y) = ½ Σⱼ uⱼ(y)²`. -/
theorem hasFDerivAt_energy {u : V3 → V3} {L : V3 →L[ℝ] V3} {x : V3}
    (hu : HasFDerivAt u L x) :
    HasFDerivAt (fun y => (1 / 2 : ℝ) * ∑ j, u y j ^ 2)
      ((1 / 2 : ℝ) • ∑ j : Fin 3, (2 * u x j) • ((ContinuousLinearMap.proj j).comp L)) x := by
  apply HasFDerivAt.const_mul
  apply HasFDerivAt.fun_sum
  intro j _
  have hj : HasFDerivAt (fun y => u y j) ((ContinuousLinearMap.proj j).comp L) x :=
    HasFDerivAt.comp x (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).hasFDerivAt hu
  have := hj.pow 2
  simpa [pow_one, mul_comm] using this

/-- **Lamb identity for differentiable fields**: `(u·∇)u = ∇(|u|²/2) - u × curl u`,
where `(u·∇)u = Du(x)[u(x)]`, `∇(|u|²/2)ᵢ = D e(x)[eᵢ]`, `curl u = curlJ (Du(x))`. -/
theorem lamb {u : V3 → V3} {L : V3 →L[ℝ] V3} {x : V3} (hu : HasFDerivAt u L x) :
    L (u x) = (fun i => fderiv ℝ (fun y => (1 / 2 : ℝ) * ∑ j, u y j ^ 2) x (Pi.single i 1))
      - cross (u x) (curlJ (jac L)) := by
  rw [(hasFDerivAt_energy hu).fderiv, apply_eq_jac_mulVec, lamb_matrix]
  congr 1
  funext i
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, mulVec, dotProduct, transpose_apply, jac, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _; ring

/-- **Beltrami mechanism**: if `curl u = λ u` at `x`, the advective term is a pure gradient:
`(u·∇)u = ∇(|u|²/2)`.  Hence `p = -|u|²/2` (+ const) balances it, and the Navier–Stokes
dynamics restricted to a Beltrami eigenspace is linear. -/
theorem beltrami_advection_is_gradient {u : V3 → V3} {L : V3 →L[ℝ] V3} {x : V3}
    (hu : HasFDerivAt u L x) (c : ℝ) (hB : curlJ (jac L) = c • u x) :
    L (u x) = fun i => fderiv ℝ (fun y => (1 / 2 : ℝ) * ∑ j, u y j ^ 2) x (Pi.single i 1) := by
  rw [lamb hu, hB, cross_smul_self, sub_zero]

end FBS3R.Lamb
