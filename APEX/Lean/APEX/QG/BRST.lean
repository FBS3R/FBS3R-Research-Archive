import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.FinCases
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Finite-dimensional toy of the BRST mechanism for constraints

`R` is a commutative ring, `V` an `R`-module, `G : Fin n → V →ₗ[R] V` constraint operators.

## 1. Abelian Koszul/BRST differential (all ghost degrees)
Cochains `ω : Finset (Fin n) → V` model `Λ(Rⁿ) ⊗ V` (`ω S` is the coefficient of
`c^{s₁} ∧ … ∧ c^{s_k}`, `S = {s₁ < … < s_k}`, ghost number `#S`). Sign
`eps a S = (-1)^{#{b ∈ S | b < a}}` and
`(Q ω)(S) = ∑_{a ∈ S} eps a (S∖a) • G_a (ω (S∖a))` (i.e. `Q = ∑_a c^a G_a`).
* `Q_sq_zero_iff`: `(∀ ω, Q (Q ω) = 0) ↔ ∀ a b, G_a ∘ G_b = G_b ∘ G_a` (no hypothesis on `V`;
  "only if" by evaluating `Q²` of the constant cochain at `S = {a,b}`, `Q_Q_pair`).
* `H0_koszul`: for a ghost-number-zero cochain `ι0 v` (`v` at `S = ∅`, `0` elsewhere),
  `Q (ι0 v) = 0 ↔ ∀ a, G_a v = 0`; as there are no cochains of negative degree,
  `H⁰ = ⋂_a ker G_a` (physical states satisfy all constraints).

## 2. Non-abelian closed algebra: Chevalley–Eilenberg differential (degrees 0 → 1 → 2 → 3)
Cochains as plain functions: `d0 v a = G_a v`,
`d1 u a b = G_a u_b − G_b u_a − ∑_c f_ab^c u_c` (the ghost term `−½ f c c ∂/∂c`),
`d2 ω x y z = G_x ω_yz − G_y ω_xz + G_z ω_xy − ∑_c f_xy^c ω_cz + ∑_c f_xz^c ω_cy − ∑_c f_yz^c ω_cx`.
`Closure G f : [G_a,G_b] = ∑_c f_ab^c G_c`; `Jacobi f` (cyclic form); `Antisymm f`.
* `d1_d0_iff`: `(∀ v, d1 (d0 v) = 0) ↔ Closure G f` (any `f`).
* `d2_d1_eq_zero`: `Closure G f`, `Jacobi f`, `Antisymm f` ⇒ `d2 (d1 u) = 0` for all `u`.
  So `Q² = 0` on ghost degrees 0 and 1 (for `n = 2` these are all degrees that matter on
  antisymmetric cochains). Higher degrees are **not** treated.
* `closure_zero_iff`: with `f = 0` closure is commutativity (consistent with §1).
* **Open algebra no-go.** `no_CE_of_not_closed`: if for some `a,b` the commutator `[G_a,G_b]`
  is not an `R`-linear combination of the `G_c`, then for **every** choice of constants `f`
  some `v` has `d1 (d0 v) ≠ 0` (the CE ansatz is never nilpotent). `open_example`: explicit
  instance `G₀ = E₁₂`, `G₁ = E₂₁` on `ℝ²` (`[G₀,G₁] = diag(1,-1)`).
* `H0_CE`: `d0 v = 0 ↔ ∀ a, G_a v = 0`.

## Caveats
Gravity's hypersurface-deformation (Dirac) algebra closes with **structure functions**
(field-dependent `f`), i.e. it is an open/soft algebra: the finite-dimensional constant-`f`
CE construction does not apply directly, and the BV/BFV formalism with higher-order ghost
terms is needed. Nothing here constructs quantum gravity; the existence, positivity or
unitarity of a physical inner product on `H⁰` is **not** addressed.
-/

namespace APEX.QG.BRST

open Finset

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V] {n : ℕ}

/-! ### 1. Abelian Koszul differential -/

/-- `eps a S = (-1)^{#{b ∈ S | b < a}}`. -/
def eps (R : Type*) [CommRing R] (a : Fin n) (S : Finset (Fin n)) : R :=
  (-1) ^ (S.filter (· < a)).card

/-- Koszul/BRST differential `Q = ∑_a c^a G_a`. -/
def Q (G : Fin n → V →ₗ[R] V) (ω : Finset (Fin n) → V) : Finset (Fin n) → V :=
  fun S => ∑ a ∈ S, eps R a (S.erase a) • G a (ω (S.erase a))

lemma eps_erase_lt {x y : Fin n} {S : Finset (Fin n)} (hy : y ∈ S) (hyx : y < x) :
    eps R x (S.erase y) = - eps R x S := by
  unfold eps
  have hm : y ∈ S.filter (· < x) := mem_filter.2 ⟨hy, hyx⟩
  rw [filter_erase, card_erase_of_mem hm]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (card_pos.2 ⟨y, hm⟩).ne'
  rw [hk, Nat.succ_sub_one, pow_succ]; ring

lemma eps_erase_not_lt {x y : Fin n} {S : Finset (Fin n)} (hyx : ¬ y < x) :
    eps R x (S.erase y) = eps R x S := by
  unfold eps
  rw [filter_erase, erase_eq_of_notMem (by simp [hyx])]

lemma coeff_antisymm {a b : Fin n} {S : Finset (Fin n)} (hS : a ∈ S) (hab : a < b) :
    eps R a (S.erase a) * eps R b ((S.erase a).erase b) =
      -(eps R b (S.erase b) * eps R a ((S.erase b).erase a)) := by
  have haS : a ∈ S.erase b := mem_erase.2 ⟨hab.ne, hS⟩
  rw [eps_erase_not_lt (lt_irrefl a), erase_right_comm, eps_erase_lt haS hab,
    eps_erase_not_lt (lt_irrefl a), eps_erase_not_lt (not_lt.2 hab.le)]
  ring

lemma Q_Q_apply (G : Fin n → V →ₗ[R] V) (ω : Finset (Fin n) → V) (S : Finset (Fin n)) :
    Q G (Q G ω) S = ∑ a ∈ S, ∑ b ∈ S.erase a,
      (eps R a (S.erase a) * eps R b ((S.erase a).erase b)) •
        G a (G b (ω ((S.erase a).erase b))) := by
  simp only [Q, map_sum, map_smul, smul_sum, smul_smul]

/-- `Q² = 0` if the constraints commute. -/
theorem Q_sq_zero_of_comm {G : Fin n → V →ₗ[R] V} (hc : ∀ a b, G a ∘ₗ G b = G b ∘ₗ G a)
    (ω : Finset (Fin n) → V) : Q G (Q G ω) = 0 := by
  funext S
  rw [Q_Q_apply, Pi.zero_apply]
  set t : Fin n → Fin n → V := fun a b =>
    (eps R a (S.erase a) * eps R b ((S.erase a).erase b)) • G a (G b (ω ((S.erase a).erase b)))
  have hpair : ∀ a b, a ∈ S → a < b → t a b + t b a = 0 := by
    intro a b ha hab
    have hcomm : G b (G a (ω ((S.erase a).erase b))) = G a (G b (ω ((S.erase a).erase b))) := by
      have := LinearMap.congr_fun (hc b a) (ω ((S.erase a).erase b))
      simpa using this
    simp only [t]
    rw [erase_right_comm (s := S) (a := b) (b := a), hcomm, coeff_antisymm ha hab,
      ← erase_right_comm (s := S) (a := b) (b := a)]
    rw [neg_smul, neg_add_cancel]
  have h1 : ∀ a ∈ S, ∑ b ∈ S.erase a, t a b = ∑ b ∈ S, (if a = b then 0 else t a b) := by
    intro a ha
    rw [← add_sum_erase S _ ha]
    simp only [↓reduceIte, zero_add]
    refine sum_congr rfl fun b hb => ?_
    simp [(ne_of_mem_erase hb).symm]
  rw [sum_congr rfl h1, ← sum_product' S S (fun a b => if a = b then 0 else t a b)]
  refine sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    rw [mem_product] at hp
    simp only [Prod.swap]
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, Ne.symm hab, ↓reduceIte]
      rcases lt_or_gt_of_ne hab with h | h
      · exact hpair a b hp.1 h
      · rw [add_comm]; exact hpair b a hp.2 h
  · rintro ⟨a, b⟩ _ hne h
    apply hne
    simp only [Prod.swap, Prod.mk.injEq] at h
    simp [h.2]
  · rintro ⟨a, b⟩ hp
    rw [mem_product] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · rintro p _; exact Prod.swap_swap p

/-- Explicit value of `Q²` on a two-element set. -/
lemma Q_Q_pair (G : Fin n → V →ₗ[R] V) (ω : Finset (Fin n) → V) {a b : Fin n} (hab : a < b) :
    Q G (Q G ω) {a, b} = G a (G b (ω ∅)) - G b (G a (ω ∅)) := by
  have e1 : ({a, b} : Finset (Fin n)).erase a = {b} := erase_insert (by simp [hab.ne])
  have e2 : ({a, b} : Finset (Fin n)).erase b = {a} := by
    rw [erase_insert_of_ne hab.ne, erase_singleton]; rfl
  rw [Q_Q_apply, sum_pair hab.ne, e1, e2, sum_singleton, sum_singleton, erase_singleton,
    erase_singleton]
  have h1 : eps R a ({b} : Finset (Fin n)) = 1 := by
    simp [eps, filter_singleton, not_lt.2 hab.le]
  have h2 : eps R b ({a} : Finset (Fin n)) = -1 := by
    simp [eps, filter_singleton, hab]
  have h3 : ∀ x : Fin n, eps R x (∅ : Finset (Fin n)) = 1 := fun x => by simp [eps]
  rw [h1, h2, h3, h3]
  simp [sub_eq_add_neg]

/-- **Abelian BRST nilpotency.** `Q² = 0 ⇔` all constraints commute. -/
theorem Q_sq_zero_iff (G : Fin n → V →ₗ[R] V) :
    (∀ ω, Q G (Q G ω) = 0) ↔ ∀ a b, G a ∘ₗ G b = G b ∘ₗ G a := by
  constructor
  · intro h a b
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have := congrFun (h fun _ => v) {a, b}
      rw [Q_Q_pair G _ hab, Pi.zero_apply] at this
      exact sub_eq_zero.1 this
    · rfl
    · have := congrFun (h fun _ => v) {b, a}
      rw [Q_Q_pair G _ hab, Pi.zero_apply] at this
      exact (sub_eq_zero.1 this).symm
  · exact fun hc ω => Q_sq_zero_of_comm hc ω

/-- Ghost-number-zero cochain. -/
def ι0 (v : V) : Finset (Fin n) → V := fun S => if S = ∅ then v else 0

/-- **`H⁰ = ⋂ ker G_a`** (Koszul model). -/
theorem H0_koszul (G : Fin n → V →ₗ[R] V) (v : V) :
    Q G (ι0 v) = 0 ↔ ∀ a, G a v = 0 := by
  constructor
  · intro h a
    have := congrFun h {a}
    simpa [Q, ι0, eps] using this
  · intro h
    funext S
    simp only [Q, Pi.zero_apply]
    refine sum_eq_zero fun a _ => ?_
    simp only [ι0]
    split_ifs <;> simp [h]

/-! ### 2. Chevalley–Eilenberg differential for a closed algebra -/

def d0 (G : Fin n → V →ₗ[R] V) (v : V) : Fin n → V := fun a => G a v

def d1 (G : Fin n → V →ₗ[R] V) (f : Fin n → Fin n → Fin n → R) (u : Fin n → V) :
    Fin n → Fin n → V :=
  fun a b => G a (u b) - G b (u a) - ∑ c, f a b c • u c

def d2 (G : Fin n → V →ₗ[R] V) (f : Fin n → Fin n → Fin n → R) (ω : Fin n → Fin n → V) :
    Fin n → Fin n → Fin n → V :=
  fun x y z => G x (ω y z) - G y (ω x z) + G z (ω x y) - ∑ c, f x y c • ω c z
    + ∑ c, f x z c • ω c y - ∑ c, f y z c • ω c x

/-- Closure `[G_a, G_b] = ∑_c f_ab^c G_c` with constant structure constants. -/
def Closure (G : Fin n → V →ₗ[R] V) (f : Fin n → Fin n → Fin n → R) : Prop :=
  ∀ a b v, G a (G b v) - G b (G a v) = ∑ c, f a b c • G c v

def Jacobi (f : Fin n → Fin n → Fin n → R) : Prop :=
  ∀ x y z d, ∑ c, (f x y c * f c z d + f y z c * f c x d + f z x c * f c y d) = 0

def Antisymm (f : Fin n → Fin n → Fin n → R) : Prop := ∀ a b c, f a b c = - f b a c

/-- `Q² = 0` on ghost degree 0 iff the algebra closes with constants `f`. -/
theorem d1_d0_iff (G : Fin n → V →ₗ[R] V) (f : Fin n → Fin n → Fin n → R) :
    (∀ v, d1 G f (d0 G v) = 0) ↔ Closure G f := by
  constructor
  · intro h a b v
    have := congrFun (congrFun (h v) a) b
    simp only [d1, d0, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  · intro h v
    funext a b
    simp only [d1, d0, Pi.zero_apply]
    rw [h a b v, sub_self]

/-- `Q² = 0` on ghost degree 1, given closure, Jacobi and antisymmetry. -/
theorem d2_d1_eq_zero {G : Fin n → V →ₗ[R] V} {f : Fin n → Fin n → Fin n → R}
    (hcl : Closure G f) (hJ : Jacobi f) (hA : Antisymm f) (u : Fin n → V) :
    d2 G f (d1 G f u) = 0 := by
  funext x y z
  simp only [d2, d1, map_sub, map_sum, map_smul, smul_sub, sum_sub_distrib, smul_sum, smul_smul,
    Pi.zero_apply]
  have h1 := hcl x y (u z)
  have h2 := hcl x z (u y)
  have h3 := hcl y z (u x)
  have hJ' : ∑ c, ∑ d, (f x y c * f c z d) • u d - ∑ c, ∑ d, (f x z c * f c y d) • u d
      + ∑ c, ∑ d, (f y z c * f c x d) • u d = 0 := by
    rw [sum_comm (f := fun c d => (f x y c * f c z d) • u d),
      sum_comm (f := fun c d => (f x z c * f c y d) • u d),
      sum_comm (f := fun c d => (f y z c * f c x d) • u d), ← sum_sub_distrib,
      ← sum_add_distrib]
    refine sum_eq_zero fun d _ => ?_
    rw [← sum_sub_distrib, ← sum_add_distrib]
    simp only [← sub_smul, ← add_smul, ← sum_smul]
    have := hJ x y z d
    have e : ∑ c, (f x y c * f c z d - f x z c * f c y d + f y z c * f c x d) =
        ∑ c, (f x y c * f c z d + f y z c * f c x d + f z x c * f c y d) := by
      refine sum_congr rfl fun c _ => ?_
      rw [hA z x c]; ring
    rw [e, this, zero_smul]
  linear_combination (norm := module) h1 - h2 + h3 + hJ'

/-- With `f = 0`, closure is commutativity. -/
theorem closure_zero_iff (G : Fin n → V →ₗ[R] V) :
    Closure G (fun _ _ _ => 0) ↔ ∀ a b, G a ∘ₗ G b = G b ∘ₗ G a := by
  constructor
  · intro h a b
    refine LinearMap.ext fun v => ?_
    have := h a b v
    simp only [zero_smul, sum_const_zero] at this
    exact sub_eq_zero.1 this
  · intro h a b v
    have := LinearMap.congr_fun (h a b) v
    simp only [LinearMap.comp_apply] at this
    simp [this]

/-- **Open-algebra no-go.** If some `[G_a, G_b]` is not a constant linear combination of the
`G_c`, then for every choice of constants `f` the CE ansatz has `d1 ∘ d0 ≠ 0`. -/
theorem no_CE_of_not_closed (G : Fin n → V →ₗ[R] V) (a b : Fin n)
    (hopen : ∀ k : Fin n → R, G a ∘ₗ G b - G b ∘ₗ G a ≠ ∑ c, k c • G c)
    (f : Fin n → Fin n → Fin n → R) : ∃ v, d1 G f (d0 G v) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hcl := (d1_d0_iff G f).1 hcon
  apply hopen (f a b)
  refine LinearMap.ext fun v => ?_
  simpa using hcl a b v

/-- `E₁₂` on `ℝ²`: `v ↦ (v₁, 0)`. -/
def E12 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := fun i => if i = 0 then v 1 else 0
  map_add' x y := by funext i; split_ifs <;> simp [*]
  map_smul' c x := by funext i; split_ifs <;> simp [*]

/-- `E₂₁` on `ℝ²`: `v ↦ (0, v₀)`. -/
def E21 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := fun i => if i = 1 then v 0 else 0
  map_add' x y := by funext i; split_ifs <;> simp [*]
  map_smul' c x := by funext i; split_ifs <;> simp [*]

/-- **Explicit open algebra.** For `G = (E₁₂, E₂₁)` on `ℝ²` (commutator `diag(1,-1)`), no
constants `f` give closure, and for every `f` the CE ansatz fails: `d1 (d0 v) ≠ 0` for some `v`. -/
theorem open_example (f : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    ¬ Closure ![E12, E21] f ∧ ∃ v, d1 ![E12, E21] f (d0 ![E12, E21] v) ≠ 0 := by
  have hnc : ¬ Closure ![E12, E21] f := by
    intro h
    have := congrFun (h 0 1 (fun i => if i = 0 then 1 else 0)) 0
    simp [E12, E21, Fin.sum_univ_two] at this
  refine ⟨hnc, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hnc ((d1_d0_iff _ f).1 hcon)

/-- **`H⁰ = ⋂ ker G_a`** (CE model). -/
theorem H0_CE (G : Fin n → V →ₗ[R] V) (v : V) : d0 G v = 0 ↔ ∀ a, G a v = 0 := by
  constructor
  · intro h a; exact congrFun h a
  · intro h; funext a; exact h a

end APEX.QG.BRST

