import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Ring

/-!
# MISSION-03: the algebraic core of the general transfer law

Everything below is proved without `sorry`, custom axioms or `native_decide`.

## 1. Finite Neumann formula (`finite_neumann`, `matrix_finite_neumann`)
In any ring `A`, if `r` is a two-sided inverse of `1 - a` and `(b r)^(N+1) = 0`, then
`X = ∑_{j=0}^{N} r (b r)^j` satisfies `(1 - a - b) X = 1` and `X (1 - a - b) = 1`.
The right-inverse identity is a geometric sum in `b r`; for the left inverse we use the standard
trick `(r b)^(N+2) = r (b r)^(N+1) b = 0` and `(r b)^j r = r (b r)^j` (`rb_nilpotent`,
`rb_pow_mul`). The matrix corollary also identifies `X` with Mathlib's nonsingular inverse `⁻¹`.

## 2. The time-event ring `E = R[x₁,…,x_k]/(x₁²,…,x_k²)` (`EventRing k R`)
We use the Mathlib model `MvPolynomial (Fin k) R ⧸ (X i ^ 2)` (a commutative ring for free).
It is free over `R` with basis the square-free monomials `x_S = ∏_{i∈S} x_i`, `S ⊆ {1..k}`, and
`x_S x_T = x_{S ∪ T}` if `S ∩ T = ∅`, `0` otherwise; so it is isomorphic to the ring of functions
`Finset (Fin k) → R` with subset convolution `(f*g)(S) = ∑_{T ⊆ S} f(T) g(S \ T)`
(this isomorphism is explained here, not formalised).
The degree filtration is the ideal `eventDeg k R d`, the image of the ideal `polyDeg k R d`
spanned by monomials of total degree `≥ d`; in the subset model these are exactly the functions
with `f(S) = 0` for `card S < d`. `HasDegGE k R f d` means `f ∈ eventDeg k R d`. Proved:
* `eventDeg_mul_le`, `HasDegGE.mul`: degree `≥ d₁` times degree `≥ d₂` has degree `≥ d₁ + d₂`;
* `eventDeg_eq_bot`, `HasDegGE.eq_zero`: degree `> k` means zero (pigeonhole: a monomial of
  degree `> k` in `k` variables is divisible by some `x_i²`, `polyDeg_le_sqIdeal`);
* `eventDeg_two_pow_eq_bot`: `(E_{≥2})^(⌊k/2⌋+1) = 0`;
* `prod_deg_two_eq_zero`: a product of `j` elements of degree `≥ 2` is `0` when `2j > k`.

## 3. Transfer law
* `transfer_law_ideal`: over any commutative ring `S`, with an ideal `I`, `I^(N+1) = ⊥`, `U` with
  entries in `I`, and `R₀` a two-sided inverse of `1 - z T₀`:
  `(1 - z(T₀+U))⁻¹ = ∑_{j=0}^{N} R₀ (z U R₀)^j` (two-sided).
* `transfer_law`: the same with `N = ⌊k/2⌋` over any commutative `E`-algebra `S`, when the entries
  of `U` have degree `≥ 2` (lie in the extension of `E_{≥2}` to `S`).
* `transfer_law_powerSeries`: in `Mat_d(E[[z]])`, for *arbitrary* `T₀` (not only constant ones),
  `1 - z T₀` is invertible (`isUnit_det_one_sub_X_smul`) and
  `(1 - z(T₀+U))⁻¹ = ∑_{j=0}^{⌊k/2⌋} (1 - zT₀)⁻¹ (z U (1 - zT₀)⁻¹)^j`.

## 4. Universal denominator
* `universal_denominator_identity`: if `δ • R₀ = Adj` then
  `δ^(N+1) • ∑_{j≤N} R₀ (z U R₀)^j = ∑_{j≤N} δ^(N-j) • Adj (z U Adj)^j`.
* `universal_denominator`: for `T₀, U` with entries in `E[z]` (`U` of degree `≥ 2`) and
  `δ = det(1 - z T₀)`, `δ^(⌊k/2⌋+1) • (1 - z(T₀+U))⁻¹` (inverse in `Mat_d(E[[z]])`) is the image of
  the explicit polynomial matrix `∑_j δ^(⌊k/2⌋-j) adj(1-zT₀) (z U adj(1-zT₀))^j ∈ Mat_d(E[z])`.
  This only says that `δ^(⌊k/2⌋+1)` is *a* common denominator; nothing is claimed about whether
  the dominant pole survives (cancellation can occur).

## 5. Degree-0 part (`degZero`, `degZero_transfer`)
The projection `ε : E → R`, `x_i ↦ 0`, applied coefficientwise to `(1 - z(T₀+U))⁻¹` gives
`(1 - z ε(T₀))⁻¹`: the constant trajectories reproduce the spatial automaton.
-/

namespace APEX.Transfer

open Finset

section Neumann

variable {A : Type*} [Ring A]

/-- `(r b)^(n+2) = r (b r)^(n+1) b`. -/
theorem rb_pow_succ_succ (r b : A) (n : ℕ) :
    (r * b) ^ (n + 2) = r * (b * r) ^ (n + 1) * b := by
  induction n with
  | zero => simp [pow_succ, mul_assoc]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ (b * r) (n + 1)]
    simp only [mul_assoc]

/-- Shift identity `(r b)^j r = r (b r)^j`. -/
theorem rb_pow_mul (r b : A) (j : ℕ) : (r * b) ^ j * r = r * (b * r) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, ih, pow_succ']
    simp only [mul_assoc]

/-- The standard trick: `(b r)^(N+1) = 0` implies `(r b)^(N+2) = 0`. -/
theorem rb_nilpotent {r b : A} {N : ℕ} (h : (b * r) ^ (N + 1) = 0) :
    (r * b) ^ (N + 2) = 0 := by
  rw [rb_pow_succ_succ, h]; simp

/-- **Abstract finite Neumann formula.** In any ring, if `r` is a two-sided inverse of `1 - a`
and `(b r)^(N+1) = 0`, then `∑_{j ≤ N} r (b r)^j` is a two-sided inverse of `1 - a - b`. -/
theorem finite_neumann {a b r : A} {N : ℕ} (hr₁ : (1 - a) * r = 1) (hr₂ : r * (1 - a) = 1)
    (hnil : (b * r) ^ (N + 1) = 0) :
    (1 - a - b) * (∑ j ∈ range (N + 1), r * (b * r) ^ j) = 1 ∧
    (∑ j ∈ range (N + 1), r * (b * r) ^ j) * (1 - a - b) = 1 := by
  have hL : (1 - a - b) * r = 1 - b * r := by
    rw [sub_mul, hr₁]
  have hR : r * (1 - a - b) = 1 - r * b := by
    rw [mul_sub, hr₂]
  constructor
  · rw [Finset.mul_sum]
    have : ∀ j ∈ range (N + 1), (1 - a - b) * (r * (b * r) ^ j) = (1 - b * r) * (b * r) ^ j := by
      intro j _; rw [← mul_assoc, hL]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, mul_neg_geom_sum, hnil, sub_zero]
  · -- the left inverse `∑_{j ≤ N+1} (r b)^j r` coincides with the proposed sum
    have hX : (∑ j ∈ range (N + 1), r * (b * r) ^ j) =
        ∑ j ∈ range (N + 2), (r * b) ^ j * r := by
      rw [Finset.sum_range_succ _ (N + 1), rb_pow_mul, hnil, mul_zero, add_zero]
      exact Finset.sum_congr rfl fun j _ => (rb_pow_mul r b j).symm
    rw [hX, Finset.sum_mul]
    have : ∀ j ∈ range (N + 2), (r * b) ^ j * r * (1 - a - b) = (r * b) ^ j * (1 - r * b) := by
      intro j _; rw [mul_assoc, hR]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, geom_sum_mul_neg, rb_nilpotent hnil,
      sub_zero]

/-- Corollary: `1 - a - b` is a unit. -/
theorem finite_neumann_isUnit {a b r : A} {N : ℕ} (hr₁ : (1 - a) * r = 1)
    (hr₂ : r * (1 - a) = 1) (hnil : (b * r) ^ (N + 1) = 0) : IsUnit (1 - a - b) :=
  let h := finite_neumann hr₁ hr₂ hnil
  ⟨⟨_, _, h.1, h.2⟩, rfl⟩

/-- Matrix form of the finite Neumann formula, over a commutative ring `S`; the inverse is the
nonsingular inverse `⁻¹` of Mathlib. -/
theorem matrix_finite_neumann {S : Type*} [CommRing S] {d : ℕ}
    {a b r : Matrix (Fin d) (Fin d) S} {N : ℕ} (hr₁ : (1 - a) * r = 1) (hr₂ : r * (1 - a) = 1)
    (hnil : (b * r) ^ (N + 1) = 0) :
    (1 - a - b)⁻¹ = ∑ j ∈ range (N + 1), r * (b * r) ^ j ∧
    (1 - a - b) * (∑ j ∈ range (N + 1), r * (b * r) ^ j) = 1 ∧
    (∑ j ∈ range (N + 1), r * (b * r) ^ j) * (1 - a - b) = 1 := by
  have h := finite_neumann hr₁ hr₂ hnil
  exact ⟨Matrix.inv_eq_right_inv h.1, h.1, h.2⟩

end Neumann

/-! ### Matrices with entries in an ideal -/

section IdealMatrix

variable {S : Type*} [CommRing S] {d : ℕ}

/-- Entries of `M * N` lie in `I * J` if those of `M` lie in `I` and those of `N` in `J`. -/
theorem entries_mul_mem {I J : Ideal S} {M N : Matrix (Fin d) (Fin d) S}
    (hM : ∀ i j, M i j ∈ I) (hN : ∀ i j, N i j ∈ J) : ∀ i j, (M * N) i j ∈ I * J := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => Ideal.mul_mem_mul (hM i l) (hN l j)

/-- Entries of `M ^ n` lie in `I ^ n` if those of `M` lie in `I`. -/
theorem entries_pow_mem {I : Ideal S} {M : Matrix (Fin d) (Fin d) S}
    (hM : ∀ i j, M i j ∈ I) (n : ℕ) : ∀ i j, (M ^ n) i j ∈ I ^ n := by
  induction n with
  | zero => intro i j; simp
  | succ n ih => rw [pow_succ, pow_succ]; exact entries_mul_mem ih hM

/-- If `I ^ n = ⊥` and the entries of `M` lie in `I`, then `M ^ n = 0`. -/
theorem matrix_pow_eq_zero {I : Ideal S} {M : Matrix (Fin d) (Fin d) S}
    (hM : ∀ i j, M i j ∈ I) {n : ℕ} (hI : I ^ n = ⊥) : M ^ n = 0 := by
  ext i j
  have := entries_pow_mem hM n i j
  rw [hI, Ideal.mem_bot] at this
  simpa using this

/-- **Transfer law, abstract form.** Let `S` be a commutative ring, `I` an ideal with
`I ^ (N+1) = ⊥`, `z ∈ S`, `T₀, U` square matrices over `S` with the entries of `U` in `I`, and
`R₀` a two-sided inverse of `1 - z • T₀`. Then `∑_{j ≤ N} R₀ (z U R₀)^j` is a two-sided inverse
of `1 - z • (T₀ + U)` (and equals its nonsingular inverse). -/
theorem transfer_law_ideal {I : Ideal S} {N : ℕ} (hI : I ^ (N + 1) = ⊥) (z : S)
    (T₀ U R₀ : Matrix (Fin d) (Fin d) S) (hU : ∀ i j, U i j ∈ I)
    (hR₁ : (1 - z • T₀) * R₀ = 1) (hR₂ : R₀ * (1 - z • T₀) = 1) :
    (1 - z • (T₀ + U))⁻¹ = ∑ j ∈ range (N + 1), R₀ * (z • U * R₀) ^ j ∧
    (1 - z • (T₀ + U)) * (∑ j ∈ range (N + 1), R₀ * (z • U * R₀) ^ j) = 1 ∧
    (∑ j ∈ range (N + 1), R₀ * (z • U * R₀) ^ j) * (1 - z • (T₀ + U)) = 1 := by
  have hb : ∀ i j, (z • U * R₀) i j ∈ I := by
    intro i j
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => Ideal.mul_mem_right _ _ (by
      rw [Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hU i l))
  have hnil : (z • U * R₀) ^ (N + 1) = 0 := matrix_pow_eq_zero hb hI
  have he : (1 : Matrix (Fin d) (Fin d) S) - z • (T₀ + U) = 1 - z • T₀ - z • U := by
    rw [smul_add, sub_sub]
  rw [he]
  exact matrix_finite_neumann hR₁ hR₂ hnil

end IdealMatrix

/-! ### The time-event ring `R[x₁,…,x_k]/(x_i²)` -/

section EventRing

open MvPolynomial

variable (k : ℕ) (R : Type*) [CommRing R]

/-- The relation ideal `(x₁², …, x_k²)` of `R[x₁,…,x_k]`. -/
noncomputable def sqIdeal : Ideal (MvPolynomial (Fin k) R) :=
  Ideal.span (Set.range fun i : Fin k => (X i : MvPolynomial (Fin k) R) ^ 2)

/-- The time-event ring `E = R[x₁,…,x_k]/(x_i²)`. -/
abbrev EventRing := MvPolynomial (Fin k) R ⧸ sqIdeal k R

/-- The event variable `x_i` in `E`. -/
noncomputable def ev (i : Fin k) : EventRing k R := Ideal.Quotient.mk _ (X i)

theorem ev_sq (i : Fin k) : ev k R i ^ 2 = 0 := by
  rw [ev, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- Monomials of total degree `≥ d`. -/
def degMonomials (d : ℕ) : Set (MvPolynomial (Fin k) R) :=
  {p | ∃ s : Fin k →₀ ℕ, d ≤ ∑ i, s i ∧ p = monomial s 1}

/-- The ideal of polynomials all of whose monomials have total degree `≥ d`. -/
noncomputable def polyDeg (d : ℕ) : Ideal (MvPolynomial (Fin k) R) :=
  Ideal.span (degMonomials k R d)

/-- **Degree filtration** of the event ring: `eventDeg k R d` is the ideal of elements of degree
`≥ d`, i.e. the image of `polyDeg d`; equivalently the `R`-span of the square-free monomials
`x_S = ∏_{i∈S} x_i` with `card S ≥ d`. -/
noncomputable def eventDeg (d : ℕ) : Ideal (EventRing k R) :=
  (polyDeg k R d).map (Ideal.Quotient.mk (sqIdeal k R))

/-- `f` has degree `≥ d`. -/
def HasDegGE (f : EventRing k R) (d : ℕ) : Prop := f ∈ eventDeg k R d

variable {k R}

theorem polyDeg_mul_le (d₁ d₂ : ℕ) :
    polyDeg k R d₁ * polyDeg k R d₂ ≤ polyDeg k R (d₁ + d₂) := by
  rw [polyDeg, polyDeg, Ideal.span_mul_span]
  apply Ideal.span_mono
  rintro _ ⟨p, ⟨s, hs, rfl⟩, q, ⟨t, ht, rfl⟩, rfl⟩
  refine ⟨s + t, ?_, ?_⟩
  · simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]; omega
  · simp [monomial_mul_monomial]

theorem polyDeg_antitone {d e : ℕ} (h : d ≤ e) : polyDeg k R e ≤ polyDeg k R d := by
  apply Ideal.span_mono
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, le_trans h hs, rfl⟩

theorem polyDeg_zero : polyDeg k R 0 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  apply Ideal.subset_span
  exact ⟨0, by simp, by simp⟩

/-- Pigeonhole: a monomial of total degree `> k` in `k` variables is divisible by some `x_i²`. -/
theorem polyDeg_le_sqIdeal : polyDeg k R (k + 1) ≤ sqIdeal k R := by
  rw [polyDeg, Ideal.span_le]
  rintro _ ⟨s, hs, rfl⟩
  have : ∃ i, 2 ≤ s i := by
    by_contra hne
    push Not at hne
    have : ∑ i, s i ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum fun i _ => by
      have := hne i; omega
    simp at this
    omega
  obtain ⟨i, hi⟩ := this
  have hle : Finsupp.single i 2 ≤ s := by
    rw [Finsupp.single_le_iff]; exact hi
  have : (monomial s (1 : R)) = X i ^ 2 * monomial (s - Finsupp.single i 2) 1 := by
    rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le hle]
  rw [SetLike.mem_coe, this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem eventDeg_zero : eventDeg k R 0 = ⊤ := by
  rw [eventDeg, polyDeg_zero, Ideal.map_top]

/-- Degree `≥ d₁` times degree `≥ d₂` has degree `≥ d₁ + d₂`. -/
theorem eventDeg_mul_le (d₁ d₂ : ℕ) :
    eventDeg k R d₁ * eventDeg k R d₂ ≤ eventDeg k R (d₁ + d₂) := by
  rw [eventDeg, eventDeg, eventDeg, ← Ideal.map_mul]
  exact Ideal.map_mono (polyDeg_mul_le d₁ d₂)

theorem HasDegGE.mul {f g : EventRing k R} {d₁ d₂ : ℕ} (hf : HasDegGE k R f d₁)
    (hg : HasDegGE k R g d₂) : HasDegGE k R (f * g) (d₁ + d₂) :=
  eventDeg_mul_le d₁ d₂ (Ideal.mul_mem_mul hf hg)

theorem eventDeg_antitone {d e : ℕ} (h : d ≤ e) : eventDeg k R e ≤ eventDeg k R d :=
  Ideal.map_mono (polyDeg_antitone h)

/-- Degree `> k` means zero. -/
theorem eventDeg_eq_bot {d : ℕ} (h : k < d) : eventDeg k R d = ⊥ := by
  rw [eventDeg, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact le_trans (polyDeg_antitone h) polyDeg_le_sqIdeal

theorem HasDegGE.eq_zero {f : EventRing k R} {d : ℕ} (hf : HasDegGE k R f d) (h : k < d) :
    f = 0 := by
  have := eventDeg_eq_bot (R := R) h
  rw [HasDegGE, this, Ideal.mem_bot] at hf
  exact hf

theorem eventDeg_pow_le (d j : ℕ) : eventDeg k R d ^ j ≤ eventDeg k R (d * j) := by
  induction j with
  | zero => simp [eventDeg_zero]
  | succ j ih =>
    rw [pow_succ (eventDeg k R d) j, Nat.mul_succ]
    exact le_trans (Ideal.mul_mono_left ih) (eventDeg_mul_le _ _)

/-- **Key nilpotency.** `(E_{≥2})^(⌊k/2⌋+1) = 0`. -/
theorem eventDeg_two_pow_eq_bot : eventDeg k R 2 ^ (k / 2 + 1) = ⊥ := by
  rw [eq_bot_iff, ← eventDeg_eq_bot (R := R) (d := 2 * (k / 2 + 1)) (by omega)]
  exact eventDeg_pow_le 2 _

/-- **Key nilpotency, elementwise.** A product of `j` elements of degree `≥ 2` vanishes as soon as
`2 j > k` (in particular for `j > ⌊k/2⌋`). -/
theorem prod_deg_two_eq_zero {j : ℕ} (hj : k < 2 * j) (f : Fin j → EventRing k R)
    (hf : ∀ i, HasDegGE k R (f i) 2) : ∏ i, f i = 0 := by
  have hmem : ∏ i, f i ∈ ∏ _i : Fin j, eventDeg k R 2 :=
    Ideal.prod_mem_prod fun i _ => hf i
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hmem
  exact HasDegGE.eq_zero (eventDeg_pow_le 2 j hmem) hj

theorem ev_hasDeg_one (i : Fin k) : HasDegGE k R (ev k R i) 1 := by
  apply Ideal.mem_map_of_mem
  apply Ideal.subset_span
  refine ⟨Finsupp.single i 1, by simp, ?_⟩
  rw [X]

end EventRing

/-! ### The transfer law over the event ring -/

section TransferLaw

variable {k : ℕ} {R : Type*} [CommRing R] {d : ℕ}

/-- **Transfer law** over any commutative algebra `S` of the event ring (e.g. `E[z]`, `E[[z]]`):
if the entries of `U` have degree `≥ 2` (lie in the extension of `E_{≥2}`) and `R₀` is a two-sided
inverse of `1 - z T₀`, then
`(1 - z (T₀ + U))⁻¹ = ∑_{j=0}^{⌊k/2⌋} R₀ (z U R₀)^j`, as a two-sided inverse. -/
theorem transfer_law {S : Type*} [CommRing S] [Algebra (EventRing k R) S] (z : S)
    (T₀ U R₀ : Matrix (Fin d) (Fin d) S)
    (hU : ∀ i j, U i j ∈ (eventDeg k R 2).map (algebraMap (EventRing k R) S))
    (hR₁ : (1 - z • T₀) * R₀ = 1) (hR₂ : R₀ * (1 - z • T₀) = 1) :
    (1 - z • (T₀ + U))⁻¹ = ∑ j ∈ range (k / 2 + 1), R₀ * (z • U * R₀) ^ j ∧
    (1 - z • (T₀ + U)) * (∑ j ∈ range (k / 2 + 1), R₀ * (z • U * R₀) ^ j) = 1 ∧
    (∑ j ∈ range (k / 2 + 1), R₀ * (z • U * R₀) ^ j) * (1 - z • (T₀ + U)) = 1 := by
  have hI : ((eventDeg k R 2).map (algebraMap (EventRing k R) S)) ^ (k / 2 + 1) = ⊥ := by
    rw [← Ideal.map_pow, eventDeg_two_pow_eq_bot, Ideal.map_bot]
  exact transfer_law_ideal hI z T₀ U R₀ hU hR₁ hR₂

open PowerSeries in
/-- Over `E[[z]]`, `1 - z T₀` is invertible for every `T₀` (its determinant has constant term 1). -/
theorem isUnit_det_one_sub_X_smul {A : Type*} [CommRing A] (T₀ : Matrix (Fin d) (Fin d) A⟦X⟧) :
    IsUnit (1 - (X : A⟦X⟧) • T₀).det := by
  rw [isUnit_iff_constantCoeff, RingHom.map_det]
  have : (constantCoeff (R := A)).mapMatrix (1 - (X : A⟦X⟧) • T₀) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  rw [this, Matrix.det_one]
  exact isUnit_one

open PowerSeries in
/-- **Transfer law in `Mat_d(E[[z]])`.** For arbitrary `T₀` and `U` whose entries have degree
`≥ 2`, with `R₀ = (1 - z T₀)⁻¹`:
`(1 - z (T₀ + U))⁻¹ = ∑_{j=0}^{⌊k/2⌋} R₀ (z U R₀)^j`. -/
theorem transfer_law_powerSeries (T₀ U : Matrix (Fin d) (Fin d) (EventRing k R)⟦X⟧)
    (hU : ∀ i j, U i j ∈ (eventDeg k R 2).map (algebraMap (EventRing k R) (EventRing k R)⟦X⟧)) :
    (1 - (X : (EventRing k R)⟦X⟧) • (T₀ + U))⁻¹ =
      ∑ j ∈ range (k / 2 + 1), (1 - (X : (EventRing k R)⟦X⟧) • T₀)⁻¹ *
        ((X : (EventRing k R)⟦X⟧) • U * (1 - (X : (EventRing k R)⟦X⟧) • T₀)⁻¹) ^ j :=
  (transfer_law _ T₀ U _ hU (Matrix.mul_nonsing_inv _ (isUnit_det_one_sub_X_smul T₀))
    (Matrix.nonsing_inv_mul _ (isUnit_det_one_sub_X_smul T₀))).1

end TransferLaw

/-! ### Universal denominator -/

section Denominator

variable {S : Type*} [CommRing S] {d : ℕ}

theorem det_pow_smul_term (δ z : S) (R₀ Adj U : Matrix (Fin d) (Fin d) S) (h : δ • R₀ = Adj)
    (j : ℕ) : δ ^ (j + 1) • (R₀ * (z • U * R₀) ^ j) = Adj * (z • U * Adj) ^ j := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [pow_succ (z • U * R₀) j, ← mul_assoc, pow_succ δ (j + 1), mul_smul,
      ← mul_smul_comm δ (R₀ * (z • U * R₀) ^ j), ← mul_smul_comm δ (z • U) R₀, h,
      ← smul_mul_assoc, ih, pow_succ, mul_assoc]

/-- **Universal denominator identity.** If `δ • R₀ = Adj` (e.g. `δ = det M`, `Adj = adj M`,
`R₀ = M⁻¹`), then `δ^(N+1) • ∑_{j≤N} R₀ (z U R₀)^j = ∑_{j≤N} δ^(N-j) • Adj (z U Adj)^j`;
the right-hand side involves no inverse. -/
theorem universal_denominator_identity (δ z : S) (R₀ Adj U : Matrix (Fin d) (Fin d) S)
    (h : δ • R₀ = Adj) (N : ℕ) :
    δ ^ (N + 1) • ∑ j ∈ range (N + 1), R₀ * (z • U * R₀) ^ j =
      ∑ j ∈ range (N + 1), δ ^ (N - j) • (Adj * (z • U * Adj) ^ j) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← det_pow_smul_term δ z R₀ Adj U h j, smul_smul, ← pow_add]
  congr 2
  omega

theorem det_smul_inv_of_isUnit (M : Matrix (Fin d) (Fin d) S) (h : IsUnit M.det) :
    M.det • M⁻¹ = M.adjugate := by
  rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ h, one_smul]

end Denominator

section DenominatorPowerSeries

open scoped Polynomial PowerSeries

variable {k : ℕ} {R : Type*} [CommRing R] {d : ℕ}

theorem mapMatrix_smul {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (c : A)
    (M : Matrix (Fin d) (Fin d) A) : f.mapMatrix (c • M) = f c • f.mapMatrix M := by
  ext i j; simp

/-- **Universal denominator, polynomial form.** Let `T₀, U` be matrices with *polynomial* entries
in `E[z]` (`E` the event ring), the entries of `U` of degree `≥ 2`, and view them in `E[[z]]` via
`φ : E[z] → E[[z]]`. With `δ = det(1 - z T₀) ∈ E[z]`, `N = ⌊k/2⌋`,
`δ^(N+1) · (1 - z(T₀+U))⁻¹` (computed in `Mat_d(E[[z]])`) is the image of the explicit polynomial
matrix `∑_{j≤N} δ^(N-j) adj(1 - zT₀) (z U adj(1 - zT₀))^j`. No division occurs on the right.
(The determinant on the left is that of the image of `1 - z T₀`, i.e. `φ δ`.) -/
theorem universal_denominator (Tp Up : Matrix (Fin d) (Fin d) (EventRing k R)[X])
    (hU : ∀ i j, Up i j ∈ (eventDeg k R 2).map (algebraMap (EventRing k R) (EventRing k R)[X])) :
    (1 - (PowerSeries.X : (EventRing k R)⟦X⟧) •
        Polynomial.coeToPowerSeries.ringHom.mapMatrix Tp).det ^ (k / 2 + 1) •
      (1 - (PowerSeries.X : (EventRing k R)⟦X⟧) •
        (Polynomial.coeToPowerSeries.ringHom.mapMatrix Tp +
          Polynomial.coeToPowerSeries.ringHom.mapMatrix Up))⁻¹ =
    Polynomial.coeToPowerSeries.ringHom.mapMatrix
      (∑ j ∈ range (k / 2 + 1), (1 - (Polynomial.X : (EventRing k R)[X]) • Tp).det ^ (k / 2 - j) •
        ((1 - (Polynomial.X : (EventRing k R)[X]) • Tp).adjugate *
          ((Polynomial.X : (EventRing k R)[X]) • Up *
            (1 - (Polynomial.X : (EventRing k R)[X]) • Tp).adjugate) ^ j)) := by
  set φ : (EventRing k R)[X] →+* (EventRing k R)⟦X⟧ := Polynomial.coeToPowerSeries.ringHom
  have hφX : φ Polynomial.X = PowerSeries.X := by
    simp [φ, Polynomial.coeToPowerSeries.ringHom_apply]
  have hM : φ.mapMatrix (1 - (Polynomial.X : (EventRing k R)[X]) • Tp) =
      1 - (PowerSeries.X : (EventRing k R)⟦X⟧) • φ.mapMatrix Tp := by
    rw [map_sub, map_one]
    ext i j
    simp [hφX]
  have hcomp : φ.comp (algebraMap (EventRing k R) (EventRing k R)[X]) =
      algebraMap (EventRing k R) (EventRing k R)⟦X⟧ := by
    refine RingHom.ext fun a => ?_
    simp [φ, Polynomial.coeToPowerSeries.ringHom_apply]
  have hUmem : ∀ i j, φ.mapMatrix Up i j ∈
      (eventDeg k R 2).map (algebraMap (EventRing k R) (EventRing k R)⟦X⟧) := by
    intro i j
    have := Ideal.mem_map_of_mem φ (hU i j)
    rw [Ideal.map_map, hcomp] at this
    simpa using this
  rw [transfer_law_powerSeries (φ.mapMatrix Tp) (φ.mapMatrix Up) hUmem,
    universal_denominator_identity _ _ _ _ _
      (det_smul_inv_of_isUnit _ (isUnit_det_one_sub_X_smul (φ.mapMatrix Tp))), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : ∀ (c : (EventRing k R)[X]) (M : Matrix (Fin d) (Fin d) (EventRing k R)[X]),
      φ.mapMatrix (c • M) = φ c • φ.mapMatrix M := fun c M => by ext; simp
  simp only [hs, map_mul, map_pow, hφX]
  have hdet : φ (1 - (Polynomial.X : (EventRing k R)[X]) • Tp).det =
      (1 - (PowerSeries.X : (EventRing k R)⟦X⟧) • φ.mapMatrix Tp).det := by
    rw [← hM]; exact RingHom.map_det (R := (EventRing k R)[X]) (S := (EventRing k R)⟦X⟧) φ (1 - (Polynomial.X : (EventRing k R)[X]) • Tp)
  have hadj : φ.mapMatrix (1 - (Polynomial.X : (EventRing k R)[X]) • Tp).adjugate =
      (1 - (PowerSeries.X : (EventRing k R)⟦X⟧) • φ.mapMatrix Tp).adjugate := by
    rw [← hM]; exact RingHom.map_adjugate (R := (EventRing k R)[X]) (S := (EventRing k R)⟦X⟧) φ (1 - (Polynomial.X : (EventRing k R)[X]) • Tp)
  rw [hdet, hadj]

end DenominatorPowerSeries

/-! ### Constant trajectories: the degree-0 part reproduces the spatial automaton -/

section DegreeZero

open scoped PowerSeries

variable {k : ℕ} {R : Type*} [CommRing R] {d : ℕ}

/-- The degree-0 projection `ε : E → R`, `x_i ↦ 0` (constant coefficient). -/
noncomputable def degZero : EventRing k R →+* R :=
  Ideal.Quotient.lift (sqIdeal k R) MvPolynomial.constantCoeff (by
    intro a ha
    have : sqIdeal k R ≤ RingHom.ker (MvPolynomial.constantCoeff (R := R) (σ := Fin k)) := by
      rw [sqIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    exact this ha)

theorem degZero_mk (p : MvPolynomial (Fin k) R) :
    degZero (Ideal.Quotient.mk (sqIdeal k R) p) = MvPolynomial.constantCoeff p := rfl

/-- `ε` kills every element of degree `≥ 1` (hence of degree `≥ 2`). -/
theorem degZero_eq_zero {f : EventRing k R} {e : ℕ} (he : 1 ≤ e) (hf : HasDegGE k R f e) :
    degZero f = 0 := by
  have hle : eventDeg k R e ≤ RingHom.ker (degZero (k := k) (R := R)) := by
    rw [eventDeg, Ideal.map_le_iff_le_comap, polyDeg, Ideal.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have hs0 : s ≠ 0 := by
      rintro rfl; simp at hs; omega
    classical
    simp only [SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker, degZero_mk,
      MvPolynomial.constantCoeff_monomial]
    exact ite_eq_right_iff.mpr fun h => absurd h hs0
  exact hle hf

/-- **Constant trajectories.** Applying the degree-0 projection `ε` coefficientwise to the
transfer matrix `(1 - z(T₀+U))⁻¹ ∈ Mat_d(E[[z]])` gives `(1 - z ε(T₀))⁻¹ ∈ Mat_d(R[[z]])`, the
resolvent of the spatial automaton `ε(T₀)`, whenever the entries of `U` have degree `≥ 2`. -/
theorem degZero_transfer (T₀ U : Matrix (Fin d) (Fin d) (EventRing k R)⟦X⟧)
    (hU : ∀ i j, U i j ∈ (eventDeg k R 2).map (algebraMap (EventRing k R) (EventRing k R)⟦X⟧)) :
    (PowerSeries.map degZero).mapMatrix (1 - (PowerSeries.X : (EventRing k R)⟦X⟧) • (T₀ + U))⁻¹ =
      (1 - (PowerSeries.X : R⟦X⟧) • (PowerSeries.map degZero).mapMatrix T₀)⁻¹ := by
  set ψ : (EventRing k R)⟦X⟧ →+* R⟦X⟧ := PowerSeries.map degZero
  have hker : (eventDeg k R 2).map (algebraMap (EventRing k R) (EventRing k R)⟦X⟧) ≤
      RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have : degZero a = 0 := degZero_eq_zero (by norm_num) ha
    simp [RingHom.mem_ker, ψ, PowerSeries.map_C, this]
  have hψU : ψ.mapMatrix U = 0 := by
    refine Matrix.ext fun i j => ?_
    simpa [RingHom.mem_ker] using hker (hU i j)
  have hunit := isUnit_det_one_sub_X_smul (T₀ + U)
  have h1 := Matrix.mul_nonsing_inv _ hunit
  have h2 := congrArg ψ.mapMatrix h1
  rw [map_mul, map_one, map_sub, map_one] at h2
  have hX : ψ.mapMatrix ((PowerSeries.X : (EventRing k R)⟦X⟧) • (T₀ + U)) =
      (PowerSeries.X : R⟦X⟧) • ψ.mapMatrix T₀ := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (congrArg (fun M => M) hψU) i) j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply] at this
    simp [ψ, Matrix.add_apply, this]
  rw [hX] at h2
  exact (Matrix.inv_eq_right_inv h2).symm

end DegreeZero

end APEX.Transfer

