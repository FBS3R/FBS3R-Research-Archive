import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Selection logic for a discrete label `q` (no physics input)

Companion to `APEX.Cosmology.LambdaUnderdetermination`, which proves that the local
trace-free equations leave Λ as a free integration constant (a de Sitter family of all radii).
A proposed *microscopic* selector picks a discrete label `q ∈ ℤ` through
`Z_q = Tr exp(-β H_q)`, `Γ(q) = -log Z_q`, `q* = argmin Γ`.
This file proves what such a selector can and cannot do **as pure selection logic**.

**No physical `H_q` is constructed here, and no observed number (Λ, H₀, Ω_Λ, any particular
label value, …) appears anywhere.** This is the selection-logic layer only.

Conventions: `IsMinimizer Γ q :↔ ∀ n, Γ q ≤ Γ n`; `IsUniqueMinimizer Γ q :↔ ∀ n ≠ q, Γ q < Γ n`
(equivalently: minimizer and the only one, `isUniqueMinimizer_iff`);
`D2 Γ q = Γ(q+1) - 2Γ(q) + Γ(q-1)`; `DConvex Γ :↔ ∀ q, 0 ≤ D2 Γ q`,
`StrictDConvex Γ :↔ ∀ q, 0 < D2 Γ q`;
`Coercive Γ :↔ ∀ M, ∃ N : ℕ, ∀ q, N < |q| → M < Γ q` (i.e. `Γ q → ∞` as `|q| → ∞`).

## 1. Existence
* `exists_minimizer_of_finite`: if there are `q₀` and a finite set `S` with `Γ q > Γ q₀`
  for all `q ∉ S`, a minimizer exists.
* `exists_minimizer_of_coercive`: every coercive `Γ : ℤ → ℝ` has a minimizer.
* `exists_minimizer_nat`: every `Γ : ℕ → ℝ` with `Γ q → ∞` (filter `atTop`) has a minimizer
  (bounded-below is then automatic).

## 2. Discrete convexity
* `minimizers_ordConnected`: for discretely convex `Γ` the minimizer set is an interval of
  integers (`Set.OrdConnected`).
* `strict_minimizers_adjacent`: under strict discrete convexity two minimizers differ by at
  most one; `strict_at_most_two`: among any three minimizers two coincide.
* `tie_example`: `Γ(q) = (q - 1/2)²` has `D2 Γ ≡ 2 > 0` and minimizer set exactly `{0, 1}`:
  strict discrete convexity does **not** imply uniqueness.
* `strict_unique_iff`: for strictly convex `Γ` with minimizer `q*`,
  `q*` is the unique minimizer ⟺ `Γ(q*-1) ≠ Γ(q*)` and `Γ(q*+1) ≠ Γ(q*)`;
  `strict_unique_iff_of_least`: if `q*` is the least minimizer, uniqueness ⟺
  `Γ(q*+1) ≠ Γ(q*)` (exact characterization by the adjacent pair).
* `quadratic_unique_iff`: for `Γ(q) = a (q - v)² + c` with `a > 0`, a unique minimizer exists
  ⟺ the continuous vertex `v` is not a half-integer.

## 3. Stability
* `gap_exists`: coercive + unique minimizer `q*` ⟹ the gap
  `δ = min_{q ≠ q*} (Γ q - Γ q*)` is attained at some `q₁ ≠ q*` and is `> 0`.
* `stable_of_gap`: if `Γ q ≥ Γ q* + δ` for all `q ≠ q*`, `δ > 0`, then every `Γ'` with
  `|Γ' q - Γ q| < δ/2` for all `q` has `q*` as unique minimizer.
* `tie_at_half_gap`: sharpness: if the gap is attained at `q₁`, a perturbation with
  `|Γ' - Γ| ≤ δ/2` everywhere makes both `q*` and `q₁` minimizers.
* `stable_selection`: the two combined under coercivity + uniqueness.

## 4. Partition sums (Gibbs soft-min)
For finitely many energies `E : ι → ℝ` (eigenvalues of `H_q`; we take the eigenvalues as data
— the spectral identity `Tr e^{-βH} = Σ e^{-β E_i}` for a Hermitian matrix is *not*
formalized here), `Z = Σ_i exp(-β E_i)`, `Γ = -log Z`:
* `Z_pos`: `Z > 0`.
* `softmin_bounds`: for `β > 0` and a ground-state index `i₀`,
  `E_{i₀} - log |ι| / β ≤ Γ/β ≤ E_{i₀}`.
* `ground_state_selection`: if dimensions are uniformly bounded by `N` and the ground energy of
  `q*` is below every other ground energy by a uniform margin `Δ > 0`, then for every
  `β > log N / Δ` the label `q*` is the unique minimizer of `Γ_β`.

## 5. No-go / minimal missing principle
* `nogo_of_invariant`: if `Γ ∘ σ = Γ` for a map `σ` with `σ q ≠ q`, then `q` is not a
  unique minimizer; `nogo_group`: if `Γ` is invariant under a group action without fixed
  points, there is no unique minimizer at all.
* `shift_invariant_const`, `nogo_shift`, `shift_invariant_not_coercive`: if `Γ(q+1) = Γ(q)`,
  then `Γ` is constant, every `q` is a minimizer, none is unique, and `Γ` is not coercive.
* `nogo_isospectral`: if the spectrum of `H_{q+1}` is a permutation of that of `H_q` (what
  unitary equivalence gives), then `Γ_β` is constant and no unique selector exists.
* `breaking_term_selects_anything`: adding the breaking term `ε (q - t)²` (`ε > 0`) to a
  shift-invariant `Γ` yields the unique minimizer `t`, for every `t`: the selected label is
  exactly the input of the breaking term.

**Minimal missing principle.** For a microscopic selector to make a prediction, one needs an
*independently justified* symmetry-breaking term in `Γ` that makes it coercive and gives a
strict gap at a unique `q*` (then `q*` is also stable under perturbations of less than half
the gap). Selection logic alone cannot supply it: with a shift symmetry nothing is selected,
and with an arbitrary breaking term anything is selected. In particular the observed value
can not be used as an input of the breaking term without making the "prediction" circular.
-/

open Finset Filter

namespace APEX.Cosmology.Selector

/-! ## Definitions -/

def IsMinimizer {α : Type*} (Γ : α → ℝ) (q : α) : Prop := ∀ n, Γ q ≤ Γ n
def IsUniqueMinimizer {α : Type*} (Γ : α → ℝ) (q : α) : Prop := ∀ n, n ≠ q → Γ q < Γ n

theorem isUniqueMinimizer_iff {α : Type*} (Γ : α → ℝ) (q : α) :
    IsUniqueMinimizer Γ q ↔ IsMinimizer Γ q ∧ ∀ m, IsMinimizer Γ m → m = q := by
  constructor
  · intro h
    refine ⟨fun n => ?_, fun m hm => ?_⟩
    · by_cases e : n = q
      · rw [e]
      · exact (h n e).le
    · by_contra e
      exact absurd (hm q) (not_le.2 (h m e))
  · rintro ⟨h1, h2⟩ n hn
    rcases (h1 n).lt_or_eq with h | h
    · exact h
    · exact absurd (h2 n (fun k => h ▸ h1 k)) hn

def D2 (Γ : ℤ → ℝ) (q : ℤ) : ℝ := Γ (q+1) - 2 * Γ q + Γ (q-1)
def DConvex (Γ : ℤ → ℝ) : Prop := ∀ q, 0 ≤ D2 Γ q
def StrictDConvex (Γ : ℤ → ℝ) : Prop := ∀ q, 0 < D2 Γ q
def Coercive (Γ : ℤ → ℝ) : Prop := ∀ M : ℝ, ∃ N : ℕ, ∀ q : ℤ, (N : ℤ) < |q| → M < Γ q

/-- forward increment -/
def inc (Γ : ℤ → ℝ) (q : ℤ) : ℝ := Γ (q+1) - Γ q

/-! ## 1. Existence -/

theorem exists_minimizer_of_finite (Γ : ℤ → ℝ) (q₀ : ℤ) (S : Finset ℤ)
    (h : ∀ q, q ∉ S → Γ q₀ < Γ q) : ∃ q, IsMinimizer Γ q := by
  obtain ⟨q, -, hq⟩ := (insert q₀ S).exists_min_image Γ ⟨q₀, mem_insert_self _ _⟩
  refine ⟨q, fun n => ?_⟩
  by_cases hn : n ∈ S
  · exact hq n (mem_insert_of_mem hn)
  · have := hq q₀ (mem_insert_self _ _); have := h n hn; linarith

lemma coercive_finite {Γ : ℤ → ℝ} (hc : Coercive Γ) (M : ℝ) :
    ∃ S : Finset ℤ, ∀ q, q ∉ S → M < Γ q := by
  obtain ⟨N, hN⟩ := hc M
  refine ⟨Finset.Icc (-(N:ℤ)) N, fun q hq => hN q ?_⟩
  rw [Finset.mem_Icc] at hq
  rcases le_or_gt 0 q with h | h
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_neg h]; omega

theorem exists_minimizer_of_coercive (Γ : ℤ → ℝ) (hc : Coercive Γ) : ∃ q, IsMinimizer Γ q := by
  obtain ⟨S, hS⟩ := coercive_finite hc (Γ 0)
  exact exists_minimizer_of_finite Γ 0 S hS

theorem exists_minimizer_nat (Γ : ℕ → ℝ) (hc : Tendsto Γ atTop atTop) :
    ∃ q, IsMinimizer Γ q := by
  obtain ⟨N, hN⟩ := (hc.eventually_gt_atTop (Γ 0)).exists_forall_of_atTop
  obtain ⟨q, -, hq⟩ := (Finset.range (N+1)).exists_min_image Γ ⟨0, by simp⟩
  refine ⟨q, fun n => ?_⟩
  by_cases hn : n < N + 1
  · exact hq n (Finset.mem_range.2 hn)
  · have h0 := hq 0 (by simp)
    have := hN n (by omega); linarith

/-! ## 2. Discrete convexity -/

lemma D2_eq (Γ : ℤ → ℝ) (q : ℤ) : D2 Γ q = inc Γ q - inc Γ (q-1) := by
  simp [D2, inc]; ring

lemma inc_succ_ge {Γ : ℤ → ℝ} (h : DConvex Γ) (q : ℤ) : inc Γ q ≤ inc Γ (q+1) := by
  have := h (q+1); rw [D2_eq] at this; simp at this; linarith

lemma inc_succ_gt {Γ : ℤ → ℝ} (h : StrictDConvex Γ) (q : ℤ) : inc Γ q < inc Γ (q+1) := by
  have := h (q+1); rw [D2_eq] at this; simp at this; linarith

lemma inc_mono {Γ : ℤ → ℝ} (h : DConvex Γ) (a : ℤ) (k : ℕ) : inc Γ a ≤ inc Γ (a + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := inc_succ_ge h (a + k)
    push_cast; rw [← add_assoc]; linarith

/-- `Γ(a+k) - Γ(a) ≥ k · inc Γ a` -/
lemma lower_bound {Γ : ℤ → ℝ} (h : DConvex Γ) (a : ℤ) (k : ℕ) :
    (k : ℝ) * inc Γ a ≤ Γ (a + k) - Γ a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm := inc_mono h a k
    have e : Γ (a + ((k+1 : ℕ) : ℤ)) = Γ (a + k) + inc Γ (a + k) := by
      simp [inc]; ring_nf
    rw [e]; push_cast; linarith

/-- `Γ(a+k) - Γ(a) ≤ k · inc Γ (a+k-1)` -/
lemma upper_bound {Γ : ℤ → ℝ} (h : DConvex Γ) (a : ℤ) (k : ℕ) :
    Γ (a + (k+1 : ℕ)) - Γ a ≤ ((k:ℝ)+1) * inc Γ (a + k) := by
  induction k with
  | zero => simp [inc]
  | succ k ih =>
    have hm := inc_succ_ge h (a + k)
    have e : Γ (a + ((k+1+1 : ℕ) : ℤ)) = Γ (a + ((k+1 : ℕ) : ℤ)) + inc Γ (a + ((k+1 : ℕ) : ℤ)) := by
      simp [inc]; ring_nf
    rw [e]; push_cast at ih hm ⊢
    rw [← add_assoc] at ih ⊢
    have h0 : (0:ℝ) ≤ (k:ℝ) + 1 := by positivity
    nlinarith

theorem minimizers_ordConnected {Γ : ℤ → ℝ} (h : DConvex Γ) :
    Set.OrdConnected {q | IsMinimizer Γ q} := by
  refine ⟨fun q₁ h1 q₂ h2 q hq => ?_⟩
  simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
  obtain ⟨hq1, hq2⟩ := hq
  intro n
  rcases hq1.lt_or_eq with hlt | rfl
  swap; · exact h1 n
  by_contra hcon
  push Not at hcon
  have hgt : Γ q₁ < Γ q := lt_of_le_of_lt (h1 n) hcon
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = q₁ + (k+1 : ℕ) := ⟨(q - q₁ - 1).toNat, by omega⟩
  have hu := upper_bound h q₁ k
  rw [← hk] at hu
  have hpos : 0 < inc Γ (q₁ + k) := by
    by_contra hneg; push Not at hneg
    have : ((k:ℝ)+1) * inc Γ (q₁+k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hq' : q = q₁ + k + 1 := by rw [hk]; push_cast; ring
  have hinc : inc Γ (q₁ + k) ≤ inc Γ q := by rw [hq']; exact inc_succ_ge h _
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q₂ = q + m := ⟨(q₂ - q).toNat, by omega⟩
  have hl := lower_bound h q m
  have : 0 ≤ (m:ℝ) * inc Γ q := mul_nonneg (by positivity) (by linarith)
  have := h2 q₁
  rw [hm] at this
  linarith

theorem strict_minimizers_adjacent {Γ : ℤ → ℝ} (h : StrictDConvex Γ) {q₁ q₂ : ℤ}
    (h1 : IsMinimizer Γ q₁) (h2 : IsMinimizer Γ q₂) (hle : q₁ ≤ q₂) : q₂ ≤ q₁ + 1 := by
  by_contra hc; push Not at hc
  have hc' : DConvex Γ := fun q => (h q).le
  have h0 : 0 ≤ inc Γ q₁ := by have := h1 (q₁+1); simp [inc]; linarith
  have hs := inc_succ_gt h q₁
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q₂ = (q₁ + 1) + (m+1 : ℕ) := ⟨(q₂ - q₁ - 2).toNat, by omega⟩
  have hl := lower_bound hc' (q₁+1) (m+1)
  have : 0 < ((m+1 : ℕ):ℝ) * inc Γ (q₁+1) := mul_pos (by positivity) (by linarith)
  have h3 := h2 (q₁+1)
  rw [← hm] at hl
  linarith

theorem strict_at_most_two {Γ : ℤ → ℝ} (h : StrictDConvex Γ) {a b c : ℤ}
    (ha : IsMinimizer Γ a) (hb : IsMinimizer Γ b) (hc : IsMinimizer Γ c) :
    a = b ∨ b = c ∨ a = c := by
  have := fun {x y} (hx : IsMinimizer Γ x) (hy : IsMinimizer Γ y) (hxy : x ≤ y) =>
    strict_minimizers_adjacent h hx hy hxy
  have h1 := this ha hb; have h2 := this hb ha
  have h3 := this hb hc; have h4 := this hc hb
  have h5 := this ha hc; have h6 := this hc ha
  omega

/-- Explicit tie: `(q - 1/2)²` is strictly discretely convex with minimizer set `{0,1}`. -/
theorem tie_example :
    StrictDConvex (fun q : ℤ => ((q:ℝ) - 1/2)^2) ∧
    (∀ q : ℤ, IsMinimizer (fun q : ℤ => ((q:ℝ) - 1/2)^2) q ↔ q = 0 ∨ q = 1) := by
  refine ⟨fun q => by simp [D2]; push_cast; nlinarith, fun q => ⟨fun hq => ?_, ?_⟩⟩
  · have h0 := hq 0
    simp only at h0; push_cast at h0
    by_contra hne; push Not at hne
    rcases le_or_gt q (-1) with h | h
    · have : (q:ℝ) ≤ -1 := by exact_mod_cast h
      nlinarith
    · have : (2:ℤ) ≤ q := by omega
      have : (2:ℝ) ≤ q := by exact_mod_cast this
      nlinarith
  · have key : ∀ n : ℤ, (1:ℝ)/4 ≤ ((n:ℝ) - 1/2)^2 := by
      intro n
      rcases le_or_gt n 0 with h | h
      · have : (n:ℝ) ≤ 0 := by exact_mod_cast h
        nlinarith
      · have : (1:ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    rintro (rfl | rfl) n <;> · have := key n; norm_num; linarith

/-- Exact characterization of uniqueness under strict convexity: only the neighbours can tie. -/
theorem strict_unique_iff {Γ : ℤ → ℝ} (h : StrictDConvex Γ) {q : ℤ} (hq : IsMinimizer Γ q) :
    IsUniqueMinimizer Γ q ↔ Γ (q-1) ≠ Γ q ∧ Γ (q+1) ≠ Γ q := by
  constructor
  · intro hu
    exact ⟨(hu (q-1) (by omega)).ne', (hu (q+1) (by omega)).ne'⟩
  · rintro ⟨hm, hp⟩
    rw [isUniqueMinimizer_iff]
    refine ⟨hq, fun m hm' => ?_⟩
    rcases le_total q m with hle | hle
    · have := strict_minimizers_adjacent h hq hm' hle
      rcases (show m = q ∨ m = q + 1 by omega) with e | e
      · exact e
      · exact absurd (le_antisymm (e ▸ hm' q) (hq (q+1))) (by rw [← e]; exact fun x => hp (e ▸ x))
    · have := strict_minimizers_adjacent h hm' hq hle
      rcases (show m = q ∨ m = q - 1 by omega) with e | e
      · exact e
      · exfalso; apply hm
        have a := hm' q; have b := hq m
        rw [← e]; linarith

/-- If `q*` is the least minimizer, uniqueness ⟺ `Γ(q*+1) ≠ Γ(q*)`. -/
theorem strict_unique_iff_of_least {Γ : ℤ → ℝ} (h : StrictDConvex Γ) {q : ℤ}
    (hq : IsMinimizer Γ q) (hleast : ∀ m, IsMinimizer Γ m → q ≤ m) :
    IsUniqueMinimizer Γ q ↔ Γ (q+1) ≠ Γ q := by
  rw [strict_unique_iff h hq]
  constructor
  · exact fun h => h.2
  · intro hp
    refine ⟨fun e => ?_, hp⟩
    have : IsMinimizer Γ (q-1) := fun n => e ▸ hq n
    have := hleast _ this; omega

/-- Quadratic case: `a (q - v)² + c` (`a > 0`) has a unique integer minimizer iff the vertex
`v` is not a half-integer. -/
theorem quadratic_unique_iff (a v c : ℝ) (ha : 0 < a) :
    (∃ q : ℤ, IsUniqueMinimizer (fun q : ℤ => a * ((q:ℝ) - v)^2 + c) q) ↔
      ∀ n : ℤ, v ≠ n + 1/2 := by
  constructor
  · rintro ⟨q, hq⟩ n rfl
    have hn : ∀ m : ℤ, (1:ℝ)/4 ≤ ((m:ℝ) - (n + 1/2))^2 := by
      intro m
      rcases le_or_gt m n with h | h
      · have : (m:ℝ) ≤ n := by exact_mod_cast h
        nlinarith
      · have : (n:ℝ) + 1 ≤ m := by exact_mod_cast h
        nlinarith
    by_cases e : q = n
    · have := hq (n+1) (by omega)
      simp only [e] at this; push_cast at this
      have : (n:ℝ) - (n + 1/2) = -1/2 := by ring
      nlinarith
    · have := hq n (Ne.symm e)
      simp only at this
      have h1 := hn q
      have : ((n:ℝ) - (n + 1/2))^2 = 1/4 := by ring
      nlinarith
  · intro hv
    set r : ℤ := ⌊v + 1/2⌋
    have h1 : (r:ℝ) ≤ v + 1/2 := Int.floor_le _
    have h2 : v + 1/2 < r + 1 := Int.lt_floor_add_one _
    have h3 : (r:ℝ) < v + 1/2 := lt_of_le_of_ne h1 (fun e => hv (r - 1) (by push_cast; linarith))
    refine ⟨r, fun m hm => ?_⟩
    simp only
    have hsq : ((r:ℝ) - v)^2 < ((m:ℝ) - v)^2 := by
      rcases lt_or_gt_of_ne hm with h | h
      · have : (m:ℝ) + 1 ≤ r := by exact_mod_cast h
        nlinarith
      · have : (r:ℝ) + 1 ≤ m := by exact_mod_cast h
        nlinarith
    nlinarith

/-! ## 3. Stability -/

theorem gap_exists (Γ : ℤ → ℝ) (hc : Coercive Γ) {q : ℤ} (hu : IsUniqueMinimizer Γ q) :
    ∃ q₁, q₁ ≠ q ∧ Γ q < Γ q₁ ∧ ∀ n, n ≠ q → Γ q₁ ≤ Γ n := by
  obtain ⟨S, hS⟩ := coercive_finite hc (Γ (q+1))
  set T := insert (q+1) (S.erase q)
  obtain ⟨q₁, hT, hmin⟩ := T.exists_min_image Γ ⟨q+1, mem_insert_self _ _⟩
  have hne : q₁ ≠ q := by
    rcases mem_insert.1 hT with e | e
    · omega
    · exact (mem_erase.1 e).1
  refine ⟨q₁, hne, hu q₁ hne, fun n hn => ?_⟩
  by_cases hnS : n ∈ S
  · exact hmin n (mem_insert_of_mem (mem_erase.2 ⟨hn, hnS⟩))
  · have := hmin (q+1) (mem_insert_self _ _); have := hS n hnS; linarith

theorem stable_of_gap (Γ Γ' : ℤ → ℝ) {q : ℤ} {δ : ℝ}
    (hgap : ∀ n, n ≠ q → Γ q + δ ≤ Γ n) (hpert : ∀ n, |Γ' n - Γ n| < δ / 2) :
    IsUniqueMinimizer Γ' q := by
  intro n hn
  have a := abs_lt.1 (hpert n); have b := abs_lt.1 (hpert q); have := hgap n hn
  linarith

theorem tie_at_half_gap (Γ : ℤ → ℝ) {q q₁ : ℤ} (hne : q₁ ≠ q) (hlt : Γ q < Γ q₁)
    (hgap : ∀ n, n ≠ q → Γ q₁ ≤ Γ n) :
    let δ := Γ q₁ - Γ q
    ∃ Γ' : ℤ → ℝ, (∀ n, |Γ' n - Γ n| ≤ δ / 2) ∧ IsMinimizer Γ' q ∧ IsMinimizer Γ' q₁ := by
  intro δ
  classical
  have hδ : 0 ≤ δ := by simp only [δ]; linarith
  let Γ' : ℤ → ℝ := fun n => if n = q then Γ q + δ/2 else if n = q₁ then Γ q₁ - δ/2 else Γ n
  have hv1 : Γ' q = Γ q + δ/2 := by simp [Γ']
  have hv2 : Γ' q₁ = Γ q + δ/2 := by simp [Γ', hne, δ]; ring
  have hge : ∀ n, Γ q + δ/2 ≤ Γ' n := by
    intro n
    by_cases e1 : n = q
    · rw [e1, hv1]
    by_cases e2 : n = q₁
    · rw [e2, hv2]
    · have := hgap n e1
      simp only [Γ', e1, e2, ite_false]
      simp only [δ] at hδ ⊢; linarith
  refine ⟨Γ', fun n => ?_, fun n => hv1 ▸ hge n, fun n => hv2 ▸ hge n⟩
  by_cases e1 : n = q
  · rw [e1, hv1, add_sub_cancel_left, abs_of_nonneg (by positivity)]
  by_cases e2 : n = q₁
  · rw [e2]; simp only [Γ', hne, ite_false, ite_true]
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
  · simp only [Γ', e1, e2, ite_false, sub_self, abs_zero]; positivity

/-- Stability and its sharpness under coercivity + uniqueness. -/
theorem stable_selection (Γ : ℤ → ℝ) (hc : Coercive Γ) {q : ℤ} (hu : IsUniqueMinimizer Γ q) :
    ∃ δ > 0, (∀ n, n ≠ q → Γ q + δ ≤ Γ n) ∧
      (∀ Γ' : ℤ → ℝ, (∀ n, |Γ' n - Γ n| < δ / 2) → IsUniqueMinimizer Γ' q) ∧
      (∃ Γ' : ℤ → ℝ, ∃ q₁, q₁ ≠ q ∧ (∀ n, |Γ' n - Γ n| ≤ δ / 2) ∧
        IsMinimizer Γ' q ∧ IsMinimizer Γ' q₁) := by
  obtain ⟨q₁, hne, hlt, hmin⟩ := gap_exists Γ hc hu
  have hgap : ∀ n, n ≠ q → Γ q + (Γ q₁ - Γ q) ≤ Γ n := fun n hn => by
    have := hmin n hn; linarith
  refine ⟨Γ q₁ - Γ q, by linarith, hgap, fun Γ' h => stable_of_gap Γ Γ' hgap h, ?_⟩
  obtain ⟨Γ', h1, h2, h3⟩ := tie_at_half_gap Γ hne hlt hmin
  exact ⟨Γ', q₁, hne, h1, h2, h3⟩

/-! ## 4. Partition sums: Gibbs soft-min -/

/-- partition sum from the spectrum `E` -/
noncomputable def Z {ι : Type*} [Fintype ι] (β : ℝ) (E : ι → ℝ) : ℝ := ∑ i, Real.exp (-β * E i)
/-- `Γ = -log Z` -/
noncomputable def Gam {ι : Type*} [Fintype ι] (β : ℝ) (E : ι → ℝ) : ℝ := -Real.log (Z β E)

theorem Z_pos {ι : Type*} [Fintype ι] [Nonempty ι] (β : ℝ) (E : ι → ℝ) : 0 < Z β E :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

theorem softmin_bounds {ι : Type*} [Fintype ι] (β : ℝ) (hβ : 0 < β) (E : ι → ℝ) (i₀ : ι)
    (hi₀ : ∀ i, E i₀ ≤ E i) :
    E i₀ - Real.log (Fintype.card ι) / β ≤ Gam β E / β ∧ Gam β E / β ≤ E i₀ := by
  haveI : Nonempty ι := ⟨i₀⟩
  have hZ := Z_pos β E
  have hlow : Real.exp (-β * E i₀) ≤ Z β E :=
    Finset.single_le_sum (f := fun i => Real.exp (-β * E i)) (fun i _ => (Real.exp_pos _).le)
      (Finset.mem_univ i₀)
  have hup : Z β E ≤ (Fintype.card ι : ℝ) * Real.exp (-β * E i₀) := by
    have : Z β E ≤ ∑ _i : ι, Real.exp (-β * E i₀) :=
      Finset.sum_le_sum fun i _ => Real.exp_le_exp.2 (by nlinarith [hi₀ i])
    simpa using this
  have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have l1 : -β * E i₀ ≤ Real.log (Z β E) := by
    rw [← Real.log_exp (-β * E i₀)]; exact Real.log_le_log (Real.exp_pos _) hlow
  have l2 : Real.log (Z β E) ≤ Real.log (Fintype.card ι) + -β * E i₀ := by
    rw [← Real.log_exp (-β * E i₀), ← Real.log_mul hc.ne' (Real.exp_pos _).ne']
    exact Real.log_le_log hZ hup
  unfold Gam
  constructor
  · rw [le_div_iff₀ hβ, sub_mul, div_mul_cancel₀ _ hβ.ne']; linarith
  · rw [div_le_iff₀ hβ]; linarith

/-- Large-β selection reduces to ground-state energies (uniform margin `Δ`, dimensions `≤ N`). -/
theorem ground_state_selection (d : ℤ → ℕ) (E : ∀ q, Fin (d q) → ℝ) (g : ∀ q, Fin (d q))
    (hg : ∀ q i, E q (g q) ≤ E q i) (N : ℕ) (hN : ∀ q, d q ≤ N) (qs : ℤ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hsep : ∀ q, q ≠ qs → E qs (g qs) + Δ ≤ E q (g q)) (β : ℝ) (hβ : 0 < β)
    (hβN : Real.log N / Δ < β) :
    IsUniqueMinimizer (fun q => Gam β (E q)) qs := by
  intro q hq
  have h1 := (softmin_bounds β hβ (E qs) (g qs) (hg qs)).2
  have h2 := (softmin_bounds β hβ (E q) (g q) (hg q)).1
  have hd : 0 < d q := Fin.pos (g q)
  have hlogle : Real.log (d q) ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hd); exact_mod_cast hN q
  have hβΔ : Real.log N < β * Δ := by rw [div_lt_iff₀ hΔ] at hβN; linarith
  have := hsep q hq
  simp only [Fintype.card_fin] at h2
  rw [div_le_iff₀ hβ] at h1
  rw [le_div_iff₀ hβ, sub_mul, div_mul_cancel₀ _ hβ.ne'] at h2
  show Gam β (E qs) < Gam β (E q)
  nlinarith

/-! ## 5. No-go and the minimal missing principle -/

theorem nogo_of_invariant {α : Type*} (Γ : α → ℝ) (σ : α → α) (hinv : ∀ q, Γ (σ q) = Γ q)
    (q : α) (hq : σ q ≠ q) : ¬ IsUniqueMinimizer Γ q := fun hu =>
  (hu (σ q) hq).ne (hinv q).symm

theorem nogo_group {G α : Type*} [Group G] [MulAction G α] (Γ : α → ℝ)
    (hinv : ∀ (g : G) q, Γ (g • q) = Γ q) (hfree : ∀ q : α, ∃ g : G, g • q ≠ q) :
    ¬ ∃ q, IsUniqueMinimizer Γ q := by
  rintro ⟨q, hu⟩
  obtain ⟨g, hg⟩ := hfree q
  exact nogo_of_invariant Γ (g • ·) (hinv g) q hg hu

theorem shift_invariant_const (Γ : ℤ → ℝ) (h : ∀ q, Γ (q+1) = Γ q) (q : ℤ) : Γ q = Γ 0 := by
  induction q using Int.induction_on with
  | zero => rfl
  | succ n ih => rw [h, ih]
  | pred n ih => rw [← ih, ← h (-(n:ℤ) - 1)]; ring_nf

theorem nogo_shift (Γ : ℤ → ℝ) (h : ∀ q, Γ (q+1) = Γ q) :
    (∀ q, IsMinimizer Γ q) ∧ ¬ ∃ q, IsUniqueMinimizer Γ q := by
  refine ⟨fun q n => by rw [shift_invariant_const Γ h q, shift_invariant_const Γ h n], ?_⟩
  rintro ⟨q, hu⟩
  exact nogo_of_invariant Γ (· + 1) h q (by omega) hu

theorem shift_invariant_not_coercive (Γ : ℤ → ℝ) (h : ∀ q, Γ (q+1) = Γ q) : ¬ Coercive Γ := by
  intro hc
  obtain ⟨N, hN⟩ := hc (Γ 0)
  have := hN (N+1) (by rw [abs_of_nonneg (by omega)]; omega)
  rw [shift_invariant_const Γ h ((N:ℤ)+1)] at this
  exact lt_irrefl _ this

/-- Isospectral family (`spec H_{q+1}` a permutation of `spec H_q`, as for unitarily
equivalent Hamiltonians): `Γ_β` is constant and no unique selector exists. -/
theorem nogo_isospectral {n : ℕ} (E : ℤ → Fin n → ℝ)
    (hiso : ∀ q, ∃ e : Equiv.Perm (Fin n), E (q+1) = E q ∘ e) (β : ℝ) :
    (∀ q, Gam β (E q) = Gam β (E 0)) ∧ ¬ ∃ q, IsUniqueMinimizer (fun q => Gam β (E q)) q := by
  have hs : ∀ q, Gam β (E (q+1)) = Gam β (E q) := by
    intro q
    obtain ⟨e, he⟩ := hiso q
    unfold Gam Z; rw [he]
    congr 2
    exact Equiv.sum_comp e (fun i => Real.exp (-β * E q i))
  exact ⟨shift_invariant_const _ hs, (nogo_shift _ hs).2⟩

/-- A breaking term `ε (q - t)²` added to a shift-invariant `Γ` selects exactly `t`,
whatever `t` is: the output is the input of the breaking term. -/
theorem breaking_term_selects_anything (Γ : ℤ → ℝ) (h : ∀ q, Γ (q+1) = Γ q) (ε : ℝ)
    (hε : 0 < ε) (t : ℤ) :
    IsUniqueMinimizer (fun q : ℤ => Γ q + ε * ((q:ℝ) - t)^2) t ∧
      Coercive (fun q : ℤ => Γ q + ε * ((q:ℝ) - t)^2) := by
  have hc := shift_invariant_const Γ h
  constructor
  · intro n hn
    simp only [hc n, hc t, sub_self]
    have : ((n:ℝ) - t) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn)
    have := pow_pos (abs_pos.2 this) 2
    rw [sq_abs] at this
    nlinarith
  · intro M
    refine ⟨(|t| + ⌈|M - Γ 0| / ε⌉₊ + 1).toNat, fun q hq => ?_⟩
    simp only [hc q]
    have hq' : |t| + ⌈|M - Γ 0| / ε⌉₊ + 1 < |q| := by omega
    have h1 : (|t| : ℝ) + ⌈|M - Γ 0| / ε⌉₊ + 1 < |(q:ℝ)| := by exact_mod_cast hq'
    have h2 : |M - Γ 0| / ε ≤ (⌈|M - Γ 0| / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (1:ℝ) + |M - Γ 0| / ε ≤ |(q:ℝ) - t| := by
      have := abs_sub_abs_le_abs_sub (q:ℝ) t
      push_cast at this; linarith
    have h4 : (1 + |M - Γ 0| / ε) ≤ ((q:ℝ) - t)^2 := by
      have h5 : 0 ≤ |M - Γ 0| / ε := by positivity
      nlinarith [sq_abs ((q:ℝ) - t), abs_nonneg ((q:ℝ) - t)]
    have h6 : ε * (|M - Γ 0| / ε) = |M - Γ 0| := by field_simp
    have h7 := le_abs_self (M - Γ 0)
    nlinarith

end APEX.Cosmology.Selector

