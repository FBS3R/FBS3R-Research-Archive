import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Geometry of `S³`: unit quaternions, `SU(2)`, the Hopf fibration, polar decomposition

Everything is proved without `sorry`.  (Mathlib's `Quaternion` module is not built in this
environment, so a small self-contained quaternion type `Q` with the Hamilton product is used.)

* **Quaternions.** `Q` (fields `a b c d`), a `Monoid` instance (associativity of the Hamilton
  product), distributivity, `normSq_mul : |pq|² = |p|²|q|²`, conjugate `qconj`.
  The unit sphere `Q.unitSphere` is closed under `*`, `1`, `qconj` (= inverse);
  `Q.unitSubmonoid`, and `Group Q.UnitQ` on the subtype of unit quaternions.
  `norm_sq_eq_normSq`: on `E4 = EuclideanSpace ℝ (Fin 4)`, `‖x‖² = normSq`;
  `mem_sphere_iff`: Euclidean `S³` = unit quaternions; `isometry_lmul`, `isometry_rmul`:
  left/right multiplication by a unit quaternion is an isometry of `ℝ⁴`, mapping `S³` to `S³`.
* **SU(2).** `toMat q = [[a+bi, c+di], [-c+di, a-bi]]`; `toMat_mul`, `toMat_add`, `toMat_one`,
  `toMat_smul`, `toMat_injective`, `det_toMat : det = normSq`, `star_toMat`.
  `unitEquivSU2 : Q.UnitQ ≃* specialUnitaryGroup (Fin 2) ℂ` (a group isomorphism; bijectivity
  in `unitToSU2_injective`, `unitToSU2_surjective`).
* **Hopf map.** `hopf (z, w) = (2 z w̄, |z|² - |w|²) ∈ ℂ × ℝ`; `hopf_normSq :
  |h(z,w)|² = (|z|²+|w|²)²`, `hopf_mapsTo : S³ → S²`, `hopf_smul` (U(1)-invariance),
  `hopf_eq_iff_exists_smul` (on `S³`, equal images iff `v' = λ v`, `|λ| = 1`),
  `hopf_surjOn` (onto `S²`), `hopf_fibres_disjoint`, `hopf_fibre_eq` (each fibre is
  `S³ ∩ span_ℝ {v, i v}`), `finrank_hopf_plane` (that span is a 2-plane): fibres are great circles.
  `toC2`, `toC2_mem_S3c_iff`: the identification `ℍ ≅ ℂ²` matching the two models of `S³`.
* **Polar decomposition.** `polar_existsUnique`: every nonzero `x ∈ ℝ⁴` is uniquely `r • u`,
  `r > 0`, `u ∈ S³`.

Not done: the linking number of two Hopf fibres.
-/

namespace APEX.S3.Hopf



/-! ## Quaternions -/

/-- Real quaternions `a + b i + c j + d k`. -/
@[ext]
structure Q where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

namespace Q

instance : Zero Q := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Q := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add Q := ⟨fun p q => ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d⟩⟩
instance : Neg Q := ⟨fun p => ⟨-p.a, -p.b, -p.c, -p.d⟩⟩
instance : Sub Q := ⟨fun p q => ⟨p.a - q.a, p.b - q.b, p.c - q.c, p.d - q.d⟩⟩
instance : SMul ℝ Q := ⟨fun r p => ⟨r * p.a, r * p.b, r * p.c, r * p.d⟩⟩
/-- Hamilton product (`i² = j² = k² = ijk = -1`). -/
instance : Mul Q := ⟨fun p q =>
  ⟨p.a * q.a - p.b * q.b - p.c * q.c - p.d * q.d,
   p.a * q.b + p.b * q.a + p.c * q.d - p.d * q.c,
   p.a * q.c - p.b * q.d + p.c * q.a + p.d * q.b,
   p.a * q.d + p.b * q.c - p.c * q.b + p.d * q.a⟩⟩

@[simp] lemma zero_a : (0 : Q).a = 0 := rfl
@[simp] lemma zero_b : (0 : Q).b = 0 := rfl
@[simp] lemma zero_c : (0 : Q).c = 0 := rfl
@[simp] lemma zero_d : (0 : Q).d = 0 := rfl
@[simp] lemma one_a : (1 : Q).a = 1 := rfl
@[simp] lemma one_b : (1 : Q).b = 0 := rfl
@[simp] lemma one_c : (1 : Q).c = 0 := rfl
@[simp] lemma one_d : (1 : Q).d = 0 := rfl
@[simp] lemma add_a (p q : Q) : (p + q).a = p.a + q.a := rfl
@[simp] lemma add_b (p q : Q) : (p + q).b = p.b + q.b := rfl
@[simp] lemma add_c (p q : Q) : (p + q).c = p.c + q.c := rfl
@[simp] lemma add_d (p q : Q) : (p + q).d = p.d + q.d := rfl
@[simp] lemma neg_a (p : Q) : (-p).a = -p.a := rfl
@[simp] lemma neg_b (p : Q) : (-p).b = -p.b := rfl
@[simp] lemma neg_c (p : Q) : (-p).c = -p.c := rfl
@[simp] lemma neg_d (p : Q) : (-p).d = -p.d := rfl
@[simp] lemma sub_a (p q : Q) : (p - q).a = p.a - q.a := rfl
@[simp] lemma sub_b (p q : Q) : (p - q).b = p.b - q.b := rfl
@[simp] lemma sub_c (p q : Q) : (p - q).c = p.c - q.c := rfl
@[simp] lemma sub_d (p q : Q) : (p - q).d = p.d - q.d := rfl
@[simp] lemma smul_a (r : ℝ) (p : Q) : (r • p).a = r * p.a := rfl
@[simp] lemma smul_b (r : ℝ) (p : Q) : (r • p).b = r * p.b := rfl
@[simp] lemma smul_c (r : ℝ) (p : Q) : (r • p).c = r * p.c := rfl
@[simp] lemma smul_d (r : ℝ) (p : Q) : (r • p).d = r * p.d := rfl
@[simp] lemma mul_a (p q : Q) : (p * q).a = p.a * q.a - p.b * q.b - p.c * q.c - p.d * q.d := rfl
@[simp] lemma mul_b (p q : Q) : (p * q).b = p.a * q.b + p.b * q.a + p.c * q.d - p.d * q.c := rfl
@[simp] lemma mul_c (p q : Q) : (p * q).c = p.a * q.c - p.b * q.d + p.c * q.a + p.d * q.b := rfl
@[simp] lemma mul_d (p q : Q) : (p * q).d = p.a * q.d + p.b * q.c - p.c * q.b + p.d * q.a := rfl

/-- Quaternion multiplication is associative and unital. -/
instance : Monoid Q where
  mul_assoc p q r := by ext <;> simp <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp

theorem mul_add (p q r : Q) : p * (q + r) = p * q + p * r := by ext <;> simp <;> ring
theorem add_mul (p q r : Q) : (p + q) * r = p * r + q * r := by ext <;> simp <;> ring
theorem mul_sub (p q r : Q) : p * (q - r) = p * q - p * r := by ext <;> simp <;> ring
theorem sub_mul (p q r : Q) : (p - q) * r = p * r - q * r := by ext <;> simp <;> ring
theorem mul_smul_comm (s : ℝ) (p q : Q) : p * (s • q) = s • (p * q) := by
  ext <;> simp <;> ring
theorem smul_mul_assoc (s : ℝ) (p q : Q) : (s • p) * q = s • (p * q) := by
  ext <;> simp <;> ring

/-- Quaternionic conjugate. -/
def qconj (p : Q) : Q := ⟨p.a, -p.b, -p.c, -p.d⟩

@[simp] lemma conj_a (p : Q) : (qconj p).a = p.a := rfl
@[simp] lemma conj_b (p : Q) : (qconj p).b = -p.b := rfl
@[simp] lemma conj_c (p : Q) : (qconj p).c = -p.c := rfl
@[simp] lemma conj_d (p : Q) : (qconj p).d = -p.d := rfl

/-- The squared Euclidean norm `a² + b² + c² + d²`. -/
def normSq (p : Q) : ℝ := p.a ^ 2 + p.b ^ 2 + p.c ^ 2 + p.d ^ 2

theorem normSq_nonneg (p : Q) : 0 ≤ normSq p := by unfold normSq; positivity

/-- Multiplicativity of the quaternion norm (Euler's four-square identity). -/
theorem normSq_mul (p q : Q) : normSq (p * q) = normSq p * normSq q := by
  simp only [normSq, mul_a, mul_b, mul_c, mul_d]; ring

theorem normSq_conj (p : Q) : normSq (qconj p) = normSq p := by
  simp only [normSq, conj_a, conj_b, conj_c, conj_d]; ring

theorem conj_mul_self (p : Q) : qconj p * p = normSq p • (1 : Q) := by
  ext <;> simp [normSq] <;> ring

theorem mul_conj_self (p : Q) : p * qconj p = normSq p • (1 : Q) := by
  ext <;> simp [normSq] <;> ring

/-! ### The unit sphere `S³ ⊂ ℍ` is a group -/

/-- `S³` as the set of unit quaternions. -/
def unitSphere : Set Q := {p | normSq p = 1}

theorem one_mem_unitSphere : (1 : Q) ∈ unitSphere := by
  simp [unitSphere, normSq]

theorem mul_mem_unitSphere {p q : Q} (hp : p ∈ unitSphere) (hq : q ∈ unitSphere) :
    p * q ∈ unitSphere := by
  simp only [unitSphere, Set.mem_ofPred_eq] at *
  rw [normSq_mul, hp, hq, one_mul]

theorem conj_mem_unitSphere {p : Q} (hp : p ∈ unitSphere) : qconj p ∈ unitSphere := by
  simp only [unitSphere, Set.mem_ofPred_eq] at *
  rw [normSq_conj, hp]

/-- For a unit quaternion, the conjugate is a two-sided inverse. -/
theorem conj_mul_of_mem {p : Q} (hp : p ∈ unitSphere) : qconj p * p = 1 := by
  rw [conj_mul_self, show normSq p = 1 from hp]; ext <;> simp

theorem mul_conj_of_mem {p : Q} (hp : p ∈ unitSphere) : p * qconj p = 1 := by
  rw [mul_conj_self, show normSq p = 1 from hp]; ext <;> simp

/-- The unit quaternions as a submonoid of `(Q, *)`. -/
def unitSubmonoid : Submonoid Q where
  carrier := unitSphere
  mul_mem' := mul_mem_unitSphere
  one_mem' := one_mem_unitSphere

/-- The type of unit quaternions. -/
abbrev UnitQ := {p : Q // p ∈ unitSphere}

/-- The unit quaternions form a group (inverse = conjugate). -/
instance : Group UnitQ where
  mul p q := ⟨p.1 * q.1, mul_mem_unitSphere p.2 q.2⟩
  one := ⟨1, one_mem_unitSphere⟩
  inv p := ⟨qconj p.1, conj_mem_unitSphere p.2⟩
  mul_assoc p q r := Subtype.ext (mul_assoc p.1 q.1 r.1)
  one_mul p := Subtype.ext (one_mul p.1)
  mul_one p := Subtype.ext (mul_one p.1)
  inv_mul_cancel p := Subtype.ext (conj_mul_of_mem p.2)

@[simp] lemma UnitQ.coe_mul (p q : UnitQ) : ((p * q : UnitQ) : Q) = p.1 * q.1 := rfl
@[simp] lemma UnitQ.coe_one : ((1 : UnitQ) : Q) = 1 := rfl
@[simp] lemma UnitQ.coe_inv (p : UnitQ) : ((p⁻¹ : UnitQ) : Q) = qconj p.1 := rfl

/-- Left multiplication by a unit quaternion preserves the norm. -/
theorem normSq_mul_left_of_unit {u : Q} (hu : u ∈ unitSphere) (p : Q) :
    normSq (u * p) = normSq p := by
  rw [normSq_mul, show normSq u = 1 from hu, one_mul]

/-- Right multiplication by a unit quaternion preserves the norm. -/
theorem normSq_mul_right_of_unit {u : Q} (hu : u ∈ unitSphere) (p : Q) :
    normSq (p * u) = normSq p := by
  rw [normSq_mul, show normSq u = 1 from hu, mul_one]

end Q

/-! ### Identification with `ℝ⁴ = EuclideanSpace ℝ (Fin 4)` -/

/-- Euclidean `ℝ⁴`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- Coordinates of a quaternion as a vector of `ℝ⁴`. -/
def toE (p : Q) : E4 := WithLp.toLp 2 ![p.a, p.b, p.c, p.d]

/-- The quaternion with the given coordinates. -/
def ofE (x : E4) : Q := ⟨x 0, x 1, x 2, x 3⟩

@[simp] lemma ofE_toE (p : Q) : ofE (toE p) = p := by
  ext <;> simp [ofE, toE]

@[simp] lemma toE_ofE (x : E4) : toE (ofE x) = x := by
  ext i; fin_cases i <;> simp [ofE, toE]

lemma ofE_sub (x y : E4) : ofE (x - y) = ofE x - ofE y := by
  ext <;> simp [ofE]

lemma ofE_smul (r : ℝ) (x : E4) : ofE (r • x) = r • ofE x := by
  ext <;> simp [ofE]

lemma ofE_add (x y : E4) : ofE (x + y) = ofE x + ofE y := by
  ext <;> simp [ofE]

lemma toE_sub (p q : Q) : toE (p - q) = toE p - toE q := by
  ext i; fin_cases i <;> simp [toE]

/-- The Euclidean norm on `ℝ⁴` is the quaternion norm. -/
theorem norm_sq_eq_normSq (x : E4) : ‖x‖ ^ 2 = Q.normSq (ofE x) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]; rfl

theorem norm_toE_sq (p : Q) : ‖toE p‖ ^ 2 = Q.normSq p := by
  rw [norm_sq_eq_normSq, ofE_toE]

/-- `S³ ⊂ ℝ⁴` (the Euclidean unit sphere) corresponds exactly to the unit quaternions. -/
theorem mem_sphere_iff (x : E4) : x ∈ Metric.sphere (0 : E4) 1 ↔ ofE x ∈ Q.unitSphere := by
  rw [mem_sphere_zero_iff_norm, Q.unitSphere, Set.mem_ofPred_eq, ← norm_sq_eq_normSq]
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have h0 := norm_nonneg x
    nlinarith [sq_nonneg (‖x‖ - 1), sq_nonneg (‖x‖ + 1)]

/-- Left multiplication by `u`, as a map `ℝ⁴ → ℝ⁴`. -/
def lmul (u : Q) (x : E4) : E4 := toE (u * ofE x)

/-- Right multiplication by `u`, as a map `ℝ⁴ → ℝ⁴`. -/
def rmul (u : Q) (x : E4) : E4 := toE (ofE x * u)

/-- Left multiplication by a unit quaternion is an isometry of `ℝ⁴`. -/
theorem isometry_lmul {u : Q} (hu : u ∈ Q.unitSphere) : Isometry (lmul u) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h : ‖lmul u x - lmul u y‖ ^ 2 = ‖x - y‖ ^ 2 := by
    rw [lmul, lmul, ← toE_sub, norm_toE_sq, ← Q.mul_sub, Q.normSq_mul_left_of_unit hu,
      norm_sq_eq_normSq, ofE_sub]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- Right multiplication by a unit quaternion is an isometry of `ℝ⁴`. -/
theorem isometry_rmul {u : Q} (hu : u ∈ Q.unitSphere) : Isometry (rmul u) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h : ‖rmul u x - rmul u y‖ ^ 2 = ‖x - y‖ ^ 2 := by
    rw [rmul, rmul, ← toE_sub, norm_toE_sq, ← Q.sub_mul, Q.normSq_mul_right_of_unit hu,
      norm_sq_eq_normSq, ofE_sub]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- Left multiplication by a unit quaternion maps `S³` into `S³`. -/
theorem lmul_mapsTo_sphere {u : Q} (hu : u ∈ Q.unitSphere) :
    Set.MapsTo (lmul u) (Metric.sphere 0 1) (Metric.sphere 0 1) := by
  intro x hx
  rw [mem_sphere_iff] at hx ⊢
  simpa [lmul] using Q.mul_mem_unitSphere hu hx

theorem rmul_mapsTo_sphere {u : Q} (hu : u ∈ Q.unitSphere) :
    Set.MapsTo (rmul u) (Metric.sphere 0 1) (Metric.sphere 0 1) := by
  intro x hx
  rw [mem_sphere_iff] at hx ⊢
  simpa [rmul] using Q.mul_mem_unitSphere hx hu

/-! ## SU(2) -/

open ComplexConjugate Matrix

/-- `a + b i + c j + d k ↦ [[a+bi, c+di], [-c+di, a-bi]]`. -/
def toMat (p : Q) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨p.a, p.b⟩, ⟨p.c, p.d⟩; ⟨-p.c, p.d⟩, ⟨p.a, -p.b⟩]

theorem toMat_mul (p q : Q) : toMat (p * q) = toMat p * toMat q := by
  rw [toMat, toMat, toMat, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp <;> ring

theorem toMat_add (p q : Q) : toMat (p + q) = toMat p + toMat q := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMat] <;> ring

theorem toMat_one : toMat 1 = 1 := by
  rw [Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMat]

theorem toMat_smul (r : ℝ) (p : Q) : toMat (r • p) = r • toMat p := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMat]

theorem toMat_injective : Function.Injective toMat := by
  intro p q h
  have h1 := congrFun (congrFun h 0) 0
  have h2 := congrFun (congrFun h 0) 1
  simp only [toMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Complex.mk.injEq] at h1 h2
  ext
  · exact h1.1
  · exact h1.2
  · exact h2.1
  · exact h2.2

/-- `toMat` as a ring homomorphism-like map: a monoid hom `Q →* M₂(ℂ)`. -/
def toMatHom : Q →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := toMat
  map_one' := toMat_one
  map_mul' := toMat_mul

theorem det_toMat (p : Q) : (toMat p).det = (Q.normSq p : ℂ) := by
  rw [toMat, Matrix.det_fin_two_of]
  simp only [Q.normSq]; push_cast
  apply Complex.ext <;> simp [sq] <;> ring

theorem star_toMat (p : Q) : star (toMat p) = toMat (Q.qconj p) := by
  rw [toMat, toMat, Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp

theorem toMat_mem_SU2 {p : Q} (hp : p ∈ Q.unitSphere) :
    toMat p ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, star_toMat,
    ← toMat_mul, Q.mul_conj_of_mem hp, toMat_one, det_toMat, show Q.normSq p = 1 from hp]
  simp

/-- The unit quaternions map homomorphically into `SU(2)`. -/
def unitToSU2 : Q.UnitQ →* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun p := ⟨toMat p.1, toMat_mem_SU2 p.2⟩
  map_one' := Subtype.ext toMat_one
  map_mul' p q := Subtype.ext (toMat_mul p.1 q.1)

theorem unitToSU2_injective : Function.Injective unitToSU2 := by
  intro p q h
  exact Subtype.ext (toMat_injective (congrArg Subtype.val h))

/-- Every element of `SU(2)` has the form `[[α, β], [-β̄, ᾱ]]`. -/
theorem SU2_form {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U 1 1 = conj (U 0 0) ∧ U 1 0 = - conj (U 0 1) := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff'] at hU
  obtain ⟨hu, hdet⟩ := hU
  rw [Matrix.det_fin_two] at hdet
  have e : ∀ i j, (star U * U) i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j => by rw [hu]
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h00 h01 h10 h11
  constructor
  · linear_combination -(U 1 1) * h00 + conj (U 0 0) * hdet + U 1 0 * h01
  · linear_combination -conj (U 0 1) * hdet + U 1 1 * h10 - U 1 0 * h11

theorem unitToSU2_surjective : Function.Surjective unitToSU2 := by
  rintro ⟨U, hU⟩
  obtain ⟨hs, hr⟩ := SU2_form hU
  let P : Q := ⟨(U 0 0).re, (U 0 0).im, (U 0 1).re, (U 0 1).im⟩
  have hP : toMat P = U := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMat, P, hs, hr]
  have hmem : P ∈ Q.unitSphere := by
    have hd := (Matrix.mem_specialUnitaryGroup_iff.1 hU).2
    rw [← hP, det_toMat] at hd
    exact_mod_cast hd
  exact ⟨⟨P, hmem⟩, Subtype.ext hP⟩

/-- The group of unit quaternions is isomorphic to `SU(2)`. -/
noncomputable def unitEquivSU2 : Q.UnitQ ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  MulEquiv.ofBijective unitToSU2 ⟨unitToSU2_injective, unitToSU2_surjective⟩

/-! ## The Hopf map -/

/-- The identification `ℍ ≅ ℂ²`, `a + bi + cj + dk ↦ (a + bi, c + di)`
(the first row of `toMat`). -/
def toC2 (p : Q) : ℂ × ℂ := (⟨p.a, p.b⟩, ⟨p.c, p.d⟩)

theorem toC2_bijective : Function.Bijective toC2 := by
  refine ⟨fun p q h => ?_, fun v => ⟨⟨v.1.re, v.1.im, v.2.re, v.2.im⟩, rfl⟩⟩
  simp only [toC2, Prod.mk.injEq, Complex.mk.injEq] at h
  ext
  exacts [h.1.1, h.1.2, h.2.1, h.2.2]

/-- `S³ ⊂ ℂ²`. -/
def S3c : Set (ℂ × ℂ) := {v | Complex.normSq v.1 + Complex.normSq v.2 = 1}

theorem toC2_mem_S3c_iff (p : Q) : toC2 p ∈ S3c ↔ p ∈ Q.unitSphere := by
  simp only [S3c, Q.unitSphere, Set.mem_ofPred_eq, toC2, Complex.normSq_mk, Q.normSq]
  constructor <;> intro h <;> linarith

/-- `S² ⊂ ℂ × ℝ ≅ ℝ³`. -/
def S2 : Set (ℂ × ℝ) := {x | Complex.normSq x.1 + x.2 ^ 2 = 1}

/-- The Hopf map `h(z, w) = (2 z w̄, |z|² - |w|²)`. -/
def hopf (v : ℂ × ℂ) : ℂ × ℝ :=
  (2 * v.1 * conj v.2, Complex.normSq v.1 - Complex.normSq v.2)

theorem hopf_normSq (v : ℂ × ℂ) :
    Complex.normSq (hopf v).1 + (hopf v).2 ^ 2 =
      (Complex.normSq v.1 + Complex.normSq v.2) ^ 2 := by
  simp only [hopf, Complex.normSq_mul, Complex.normSq_conj]
  have : Complex.normSq 2 = 4 := by simp [Complex.normSq]; norm_num
  rw [this]; ring

theorem hopf_mapsTo : Set.MapsTo hopf S3c S2 := by
  intro v hv
  simp only [S3c, S2, Set.mem_ofPred_eq] at *
  rw [hopf_normSq, hv]; norm_num

/-- `h(λz, λw) = h(z, w)` for `|λ| = 1`. -/
theorem hopf_smul {l : ℂ} (hl : Complex.normSq l = 1) (v : ℂ × ℂ) : hopf (l • v) = hopf v := by
  have hl' : l * conj l = 1 := by rw [Complex.mul_conj, hl]; simp
  simp only [hopf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul, hl,
    one_mul, Prod.mk.injEq, and_true]
  linear_combination (2 * v.1 * conj v.2) * hl'

/-- Conversely, two points of `S³` with the same image differ by a unit scalar. -/
theorem hopf_eq_iff_exists_smul {v v' : ℂ × ℂ} (hv : v ∈ S3c) (hv' : v' ∈ S3c) :
    hopf v = hopf v' ↔ ∃ l : ℂ, Complex.normSq l = 1 ∧ v' = l • v := by
  constructor
  · intro h
    obtain ⟨z, w⟩ := v
    obtain ⟨z', w'⟩ := v'
    simp only [S3c, Set.mem_ofPred_eq] at hv hv'
    simp only [hopf, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hzw : z * conj w = z' * conj w' := by linear_combination h1 / 2
    have hzw' : conj z * w = conj z' * w' := by
      have := congrArg conj hzw
      simpa using this
    have hzr : Complex.normSq z = Complex.normSq z' := by linarith
    have hwr : Complex.normSq w = Complex.normSq w' := by linarith
    have hz : z * conj z = z' * conj z' := by
      rw [Complex.mul_conj, Complex.mul_conj, hzr]
    have hw : w * conj w = w' * conj w' := by
      rw [Complex.mul_conj, Complex.mul_conj, hwr]
    have hS' : z' * conj z' + w' * conj w' = 1 := by
      rw [Complex.mul_conj, Complex.mul_conj]; exact_mod_cast hv'
    set l := z' * conj z + w' * conj w with hl
    have e1 : l * z = z' := by
      rw [hl]; linear_combination w' * hzw + z' * hz + z' * hS'
    have e2 : l * w = w' := by
      rw [hl]; linear_combination z' * hzw' + w' * hw + w' * hS'
    refine ⟨l, ?_, ?_⟩
    · have : Complex.normSq z' + Complex.normSq w' = Complex.normSq l *
          (Complex.normSq z + Complex.normSq w) := by
        rw [← e1, ← e2, Complex.normSq_mul, Complex.normSq_mul]; ring
      rw [hv, hv'] at this; linarith
    · simp [e1, e2]
  · rintro ⟨l, hl, rfl⟩
    exact (hopf_smul hl v).symm

/-- The Hopf map is surjective onto `S²`. -/
theorem hopf_surjOn : Set.SurjOn hopf S3c S2 := by
  rintro ⟨p, t⟩ hx
  simp only [S2, Set.mem_ofPred_eq] at hx
  have hp0 := Complex.normSq_nonneg p
  by_cases ht : t = -1
  · subst ht
    have : Complex.normSq p = 0 := by nlinarith
    rw [Complex.normSq_eq_zero] at this
    subst this
    refine ⟨(0, 1), ?_, ?_⟩
    · simp [S3c]
    · simp [hopf]
  · have ht1 : -1 < t := by
      rcases lt_or_gt_of_ne ht with h | h
      · nlinarith
      · exact h
    set s := Real.sqrt ((1 + t) / 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
    have hss : s * s = (1 + t) / 2 := Real.mul_self_sqrt (by linarith)
    have h1t : 1 + t ≠ 0 := by linarith
    have hp : Complex.normSq p = 1 - t ^ 2 := by linarith
    refine ⟨((s : ℂ), conj p / ((2 * s : ℝ) : ℂ)), ?_, ?_⟩
    · simp only [S3c, Set.mem_ofPred_eq, Complex.normSq_ofReal, Complex.normSq_div,
        Complex.normSq_conj, hss, hp]
      field_simp
      linear_combination (2 * t - 2) * hss
    · simp only [hopf, Prod.mk.injEq, Complex.normSq_ofReal,
        Complex.normSq_conj, hss, hp, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
      constructor
      · have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
        push_cast
        field_simp
      · field_simp
        linear_combination (2 - 2 * t) * hss

/-- Fibres over distinct points are disjoint. -/
theorem hopf_fibres_disjoint {x y : ℂ × ℝ} (hxy : x ≠ y) :
    Disjoint (S3c ∩ hopf ⁻¹' {x}) (S3c ∩ hopf ⁻¹' {y}) := by
  rw [Set.disjoint_left]
  rintro v ⟨_, hx⟩ ⟨_, hy⟩
  exact hxy ((Set.mem_singleton_iff.1 hx).symm.trans (Set.mem_singleton_iff.1 hy))

lemma real_smul_add_smul_I (a b : ℝ) (v : ℂ × ℂ) :
    a • v + b • (Complex.I • v) = ((a : ℂ) + b * Complex.I) • v := by
  ext <;> simp [Complex.real_smul] <;> ring

/-- Each fibre is the intersection of `S³` with the real 2-plane `span_ℝ {v, i v}`. -/
theorem hopf_fibre_eq {v : ℂ × ℂ} (hv : v ∈ S3c) :
    S3c ∩ hopf ⁻¹' {hopf v} = S3c ∩ (Submodule.span ℝ {v, Complex.I • v} : Set (ℂ × ℂ)) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
    Submodule.mem_span_pair]
  constructor
  · rintro ⟨hx, h⟩
    obtain ⟨l, -, rfl⟩ := (hopf_eq_iff_exists_smul hv hx).1 h.symm
    refine ⟨hx, l.re, l.im, ?_⟩
    rw [real_smul_add_smul_I, Complex.re_add_im]
  · rintro ⟨hx, a, b, rfl⟩
    refine ⟨hx, ?_⟩
    rw [real_smul_add_smul_I] at hx ⊢
    set l : ℂ := (a : ℂ) + b * Complex.I
    have hl : Complex.normSq l = 1 := by
      simp only [S3c, Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        Complex.normSq_mul] at hx hv
      have : Complex.normSq l * (Complex.normSq v.1 + Complex.normSq v.2) = 1 := by
        rw [← hx]; ring
      rw [hv, mul_one] at this; exact this
    exact hopf_smul hl v

/-- The plane `span_ℝ {v, i v}` is genuinely 2-dimensional for `v ≠ 0`. -/
theorem linearIndependent_v_Iv {v : ℂ × ℂ} (hv : v ≠ 0) :
    LinearIndependent ℝ ![v, Complex.I • v] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  rw [real_smul_add_smul_I] at h
  have hl : ((a : ℂ) + b * Complex.I) = 0 := by
    by_contra hne
    exact hv ((smul_eq_zero.1 h).resolve_left hne)
  have h1 := congrArg Complex.re hl
  have h2 := congrArg Complex.im hl
  simp at h1 h2
  exact ⟨h1, h2⟩

theorem finrank_hopf_plane {v : ℂ × ℂ} (hv : v ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ {v, Complex.I • v}) = 2 := by
  have := finrank_span_eq_card (linearIndependent_v_Iv hv)
  rw [Matrix.range_cons_cons_empty] at this
  simpa using this

/-! ## Polar decomposition in `ℝ⁴` -/

theorem polar_exists {x : E4} (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ u ∈ Metric.sphere (0 : E4) 1, x = r • u := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  refine ⟨‖x‖, hn, ‖x‖⁻¹ • x, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

theorem polar_unique {r s : ℝ} {u v : E4} (hr : 0 < r) (hs : 0 < s)
    (hu : u ∈ Metric.sphere (0 : E4) 1) (hv : v ∈ Metric.sphere (0 : E4) 1)
    (h : r • u = s • v) : r = s ∧ u = v := by
  rw [mem_sphere_zero_iff_norm] at hu hv
  have hn := congrArg norm h
  rw [norm_smul, norm_smul, hu, hv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr,
    abs_of_pos hs, mul_one, mul_one] at hn
  subst hn
  exact ⟨rfl, smul_right_injective E4 hr.ne' h⟩

/-- Every nonzero `x ∈ ℝ⁴` is uniquely `r • u` with `r > 0`, `u ∈ S³`. -/
theorem polar_existsUnique {x : E4} (hx : x ≠ 0) :
    ∃! p : ℝ × E4, 0 < p.1 ∧ p.2 ∈ Metric.sphere (0 : E4) 1 ∧ x = p.1 • p.2 := by
  obtain ⟨r, hr, u, hu, rfl⟩ := polar_exists hx
  refine ⟨(r, u), ⟨hr, hu, rfl⟩, ?_⟩
  rintro ⟨s, v⟩ ⟨hs, hv, h⟩
  obtain ⟨h1, h2⟩ := polar_unique hs hr hv hu h.symm
  exact Prod.ext h1 h2

end APEX.S3.Hopf

