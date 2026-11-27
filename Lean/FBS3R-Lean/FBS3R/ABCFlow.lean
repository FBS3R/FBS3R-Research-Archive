/-
# ABC (Arnold–Beltrami–Childress) flows: explicit Beltrami solutions

Flat (ℝ³ / T³) counterpart of the archive's central mechanism "a signed curl
eigenspace is an exact reducing space of Navier–Stokes" (Killing–Beltrami papers,
2026-09).  For every `A, B, C`, the field
`U(x,y,z) = (A sin z + C cos y, B sin x + A cos z, C sin y + B cos x)`
satisfies, with genuine Fréchet derivatives:
* `curl U = U` (Beltrami with eigenvalue `1`) and `div U = 0`;
* `(U·∇)U = ∇(|U|²/2)`, i.e. `U` is a **steady Euler solution** with pressure
  `p = -|U|²/2`.
(Together with `ΔU = -U`, which is classical but not formalised here, `e^{-νt} U` is an
exact Navier–Stokes solution.)
-/
import FBS3R.LambBeltrami
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace FBS3R.ABC

open FBS3R.Lamb Real ContinuousLinearMap

variable (A B C : ℝ)

/-- The ABC field. -/
noncomputable def U (x : V3) : V3 :=
  ![A * sin (x 2) + C * cos (x 1), B * sin (x 0) + A * cos (x 2), C * sin (x 1) + B * cos (x 0)]

/-- Its derivative, row by row. -/
noncomputable def dU (x : V3) : V3 →L[ℝ] V3 :=
  ContinuousLinearMap.pi ![
    (A * cos (x 2)) • proj 2 + (C * -sin (x 1)) • proj 1,
    (B * cos (x 0)) • proj 0 + (A * -sin (x 2)) • proj 2,
    (C * cos (x 1)) • proj 1 + (B * -sin (x 0)) • proj 0]

lemma comp_sin (i : Fin 3) (x : V3) :
    HasFDerivAt (fun y : V3 => sin (y i)) (cos (x i) • (proj i : V3 →L[ℝ] ℝ)) x :=
  (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) i x).sin

lemma comp_cos (i : Fin 3) (x : V3) :
    HasFDerivAt (fun y : V3 => cos (y i)) (-sin (x i) • (proj i : V3 →L[ℝ] ℝ)) x :=
  (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) i x).cos

theorem hasFDerivAt_U (x : V3) : HasFDerivAt (U A B C) (dU A B C x) x := by
  have e : U A B C = fun y i => (![fun y : V3 => A * sin (y 2) + C * cos (y 1),
      fun y : V3 => B * sin (y 0) + A * cos (y 2),
      fun y : V3 => C * sin (y 1) + B * cos (y 0)] : Fin 3 → V3 → ℝ) i y := by
    funext y i; fin_cases i <;> rfl
  rw [e, dU, hasFDerivAt_pi]
  intro i
  fin_cases i
  · show HasFDerivAt (fun y : V3 => A * sin (y 2) + C * cos (y 1)) _ x
    convert ((comp_sin 2 x).const_mul A).fun_add ((comp_cos 1 x).const_mul C) using 1
    ext v; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]; simp; ring
  · show HasFDerivAt (fun y : V3 => B * sin (y 0) + A * cos (y 2)) _ x
    convert ((comp_sin 0 x).const_mul B).fun_add ((comp_cos 2 x).const_mul A) using 1
    ext v; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]; simp; ring
  · show HasFDerivAt (fun y : V3 => C * sin (y 1) + B * cos (y 0)) _ x
    convert ((comp_sin 1 x).const_mul C).fun_add ((comp_cos 0 x).const_mul B) using 1
    ext v; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]; simp; ring

/-- **Beltrami property** `curl U = U`. -/
theorem curl_eq (x : V3) : curlJ (jac (dU A B C x)) = U A B C x := by
  funext i
  fin_cases i <;> simp [curlJ, jac, dU, U, Pi.single_apply] <;> ring

/-- **Incompressibility** `div U = tr DU = 0`. -/
theorem div_eq_zero (x : V3) :
    jac (dU A B C x) 0 0 + jac (dU A B C x) 1 1 + jac (dU A B C x) 2 2 = 0 := by
  simp [jac, dU, Pi.single_apply]

/-- **Steady Euler**: `(U·∇)U = ∇(|U|²/2)`, so `p = -|U|²/2` balances the advection. -/
theorem steady_euler (x : V3) :
    dU A B C x (U A B C x) =
      fun i => fderiv ℝ (fun y => (1 / 2 : ℝ) * ∑ j, U A B C y j ^ 2) x (Pi.single i 1) := by
  apply beltrami_advection_is_gradient (hasFDerivAt_U A B C x) 1
  rw [curl_eq, one_smul]

end FBS3R.ABC
