import APEX.Blockade.Count
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Range-`r` blockade: the dominant root of `1 − z − z^{r+1}` and the growth of `a r n`

Notation: `Dr r x = 1 − x − x^{r+1}`, `Br r x = 1 + x + … + x^r`, `rho r` the root below,
`Kr r = ρ + (r+1)ρ^{r+1}`, `sigmaSq r = 2ρ^{r+1}/K_r`.  All results hold for every `r : ℕ`
(in particular for `r ≥ 1`; `r = 0` is the hypercube, `ρ = 1/2`).

* `exists_unique_root` : there is a unique real `ρ ∈ (0,1)` with `1 − ρ − ρ^{r+1} = 0`;
  `rho r` is that root, `rho_eq : ρ + ρ^{r+1} = 1`; `rho_unique` : any positive real root is `ρ`.
* `deriv_Dr_rho_ne_zero` : `D_r'(ρ) = −1 − (r+1)ρ^r ≠ 0` (simple root);
  `Kr_eq_neg_rho_mul_deriv` : `K_r = −ρ D_r'(ρ)`; `Kr_pos` : `K_r > 0`.
* `complex_root_norm` : every complex `z ≠ ρ` with `1 − z − z^{r+1} = 0` has `‖z‖ > ρ`;
  `complex_root_norm_ge` : every complex root has `‖z‖ ≥ ρ`.
* `Br_rho` : `B_r(ρ) = ρ^{−r}`.
* `rho_one` : `ρ_1 = φ − 1 = φ⁻¹`; `sigmaSq_one` : `2ρ_1²/K_1 = 1 − 1/√5`.
* `tendsto_of_averaging` (general): a real sequence with `u(n+r+1) = p u(n+r) + q u(n)`,
  `0 < p ≤ 1`, `q ≥ 0`, `p + q = 1`, converges to `J/(1 + r q)` where
  `J = u r + q ∑_{i<r} u i` (an invariant), with geometric rate `(1 − p^{r+1}/2)^{⌊n/(r+1)⌋}`.
* `tendsto_a_mul_rho_pow` : `a r n · ρ^n → B_r(ρ)/K_r` as `n → ∞`.
-/

namespace APEX.Blockade

open Finset

/-! ### 1. The dominant real root -/

/-- `D_r(x) = 1 − x − x^{r+1}`. -/
def Dr (r : ℕ) (x : ℝ) : ℝ := 1 - x - x ^ (r + 1)

lemma Dr_strictAnti (r : ℕ) : StrictAntiOn (Dr r) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Dr]
  have : x ^ (r + 1) < y ^ (r + 1) := pow_lt_pow_left₀ hxy hx (by omega)
  linarith

theorem exists_unique_root (r : ℕ) : ∃! ρ : ℝ, ρ ∈ Set.Ioo 0 1 ∧ Dr r ρ = 0 := by
  have hc : ContinuousOn (Dr r) (Set.Icc 0 1) := by
    unfold Dr; fun_prop
  obtain ⟨ρ, hρ, h0⟩ := intermediate_value_Icc' (zero_le_one) hc
    (show (0 : ℝ) ∈ Set.Icc (Dr r 1) (Dr r 0) by simp [Dr])
  refine ⟨ρ, ⟨⟨?_, ?_⟩, h0⟩, ?_⟩
  · rcases hρ.1.eq_or_lt with h | h
    · subst h; simp [Dr] at h0
    · exact h
  · rcases hρ.2.eq_or_lt with h | h
    · subst h; simp [Dr] at h0
    · exact h
  · rintro y ⟨hy, hy0⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := Dr_strictAnti r (Set.mem_Ici.2 hy.1.le) (Set.mem_Ici.2 hρ.1) h; linarith
    · have := Dr_strictAnti r (Set.mem_Ici.2 hρ.1) (Set.mem_Ici.2 hy.1.le) h; linarith

/-- The unique root `ρ_r ∈ (0,1)` of `1 − x − x^{r+1}`. -/
noncomputable def rho (r : ℕ) : ℝ := (exists_unique_root r).exists.choose

lemma rho_spec (r : ℕ) : rho r ∈ Set.Ioo 0 1 ∧ Dr r (rho r) = 0 :=
  (exists_unique_root r).exists.choose_spec

lemma rho_pos (r : ℕ) : 0 < rho r := (rho_spec r).1.1
lemma rho_lt_one (r : ℕ) : rho r < 1 := (rho_spec r).1.2
/-- `ρ + ρ^{r+1} = 1`. -/
lemma rho_eq (r : ℕ) : rho r + rho r ^ (r + 1) = 1 := by
  have := (rho_spec r).2; simp only [Dr] at this; linarith

lemma rho_unique (r : ℕ) {x : ℝ} (hx : 0 < x) (h : 1 - x - x ^ (r + 1) = 0) : x = rho r := by
  have hx1 : x < 1 := by
    by_contra hh; push Not at hh
    have : 0 < x ^ (r + 1) := by positivity
    linarith
  exact (exists_unique_root r).unique ⟨⟨hx, hx1⟩, h⟩ (rho_spec r)

theorem hasDerivAt_Dr (r : ℕ) (x : ℝ) :
    HasDerivAt (Dr r) (-1 - (r + 1 : ℝ) * x ^ r) x := by
  have := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x)).sub (hasDerivAt_pow (r + 1) x)
  refine this.congr_deriv ?_
  simp

/-- `ρ` is a simple root: `D_r'(ρ) = −1 − (r+1)ρ^r ≠ 0`. -/
theorem deriv_Dr_rho_ne_zero (r : ℕ) : deriv (Dr r) (rho r) = -1 - (r + 1 : ℝ) * rho r ^ r ∧
    deriv (Dr r) (rho r) ≠ 0 := by
  rw [(hasDerivAt_Dr r (rho r)).deriv]
  refine ⟨rfl, ?_⟩
  have : 0 < (r + 1 : ℝ) * rho r ^ r := by have := rho_pos r; positivity
  linarith

/-- `K_r = ρ + (r+1)ρ^{r+1}`. -/
noncomputable def Kr (r : ℕ) : ℝ := rho r + (r + 1) * rho r ^ (r + 1)

theorem Kr_eq_neg_rho_mul_deriv (r : ℕ) : Kr r = -(rho r * deriv (Dr r) (rho r)) := by
  rw [(deriv_Dr_rho_ne_zero r).1, Kr]; ring

theorem Kr_pos (r : ℕ) : 0 < Kr r := by
  have := rho_pos r; unfold Kr; positivity

/-! ### 2. Minimal modulus among complex roots -/

open ComplexOrder in
theorem complex_root_norm (r : ℕ) {z : ℂ} (hz : 1 - z - z ^ (r + 1) = 0) (hne : z ≠ rho r) :
    rho r < ‖z‖ := by
  have h1 : z + z ^ (r + 1) = 1 := by linear_combination -hz
  -- `1 = Re z + Re z^{r+1} ≤ ‖z‖ + ‖z‖^{r+1}`
  have hre : (z + z ^ (r + 1)).re = 1 := by rw [h1]; simp
  rw [Complex.add_re] at hre
  have a1 := Complex.re_le_norm z
  have a2 := Complex.re_le_norm (z ^ (r + 1))
  rw [Complex.norm_pow] at a2
  set t := ‖z‖ with ht
  have t0 : 0 ≤ t := norm_nonneg z
  have hge : 1 ≤ t + t ^ (r + 1) := by linarith
  by_contra hlt; push Not at hlt
  rcases hlt.lt_or_eq with hlt | heq
  · have : t ^ (r + 1) < rho r ^ (r + 1) := pow_lt_pow_left₀ hlt t0 (by omega)
    have := rho_eq r; linarith
  · -- equality case
    have hρ := rho_eq r
    rw [heq] at a1 a2
    have e1 : z.re = ‖z‖ := by rw [← ht, heq]; linarith
    have hz0 : (0 : ℂ) ≤ z := Complex.re_eq_norm.1 e1
    have him : z.im = 0 := (Complex.nonneg_iff.1 hz0).2.symm
    have hzre : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    apply hne
    rw [hzre, e1, ← ht, heq]

/-- Consequently `‖z‖ ≥ ρ` for every complex root, with equality only at `z = ρ`. -/
theorem complex_root_norm_ge (r : ℕ) {z : ℂ} (hz : 1 - z - z ^ (r + 1) = 0) : rho r ≤ ‖z‖ := by
  by_cases h : z = rho r
  · rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rho_pos r)]
  · exact (complex_root_norm r hz h).le

/-! ### 3. `B_r(ρ) = ρ^{-r}` -/

/-- `B_r(x) = 1 + x + … + x^r`. -/
def Br (r : ℕ) (x : ℝ) : ℝ := ∑ i ∈ range (r + 1), x ^ i

theorem Br_rho (r : ℕ) : Br r (rho r) = (rho r ^ r)⁻¹ := by
  have hρ := rho_eq r
  have h0 := rho_pos r
  have h1 := rho_lt_one r
  have hg : Br r (rho r) * (1 - rho r) = 1 - rho r ^ (r + 1) := by
    unfold Br; rw [mul_comm, ← mul_neg_geom_sum]
  have hne : rho r ^ r ≠ 0 := by positivity
  apply eq_inv_of_mul_eq_one_left
  have : (1 - rho r) = rho r * rho r ^ r := by rw [← pow_succ']; linarith
  have h2 : 1 - rho r ^ (r + 1) = rho r := by linarith
  rw [this, h2] at hg
  have : rho r * (Br r (rho r) * rho r ^ r - 1) = 0 := by linear_combination hg
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-! ### 4. The case `r = 1` -/

open Real in
theorem rho_one : rho 1 = goldenRatio - 1 ∧ rho 1 = goldenRatio⁻¹ := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 2 < Real.sqrt 5 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have e : goldenRatio - 1 = rho 1 := by
    apply rho_unique 1
    · unfold goldenRatio; linarith
    · unfold goldenRatio; linear_combination (-1/4 : ℝ) * h5
  refine ⟨e.symm, ?_⟩
  rw [← e, inv_goldenRatio]; unfold goldenRatio goldenConj; ring

/-- `σ_r² = 2ρ^{r+1}/K_r`. -/
noncomputable def sigmaSq (r : ℕ) : ℝ := 2 * rho r ^ (r + 1) / Kr r

theorem sigmaSq_one : sigmaSq 1 = 1 - 1 / Real.sqrt 5 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 5 := by positivity
  have e := rho_one.1
  unfold sigmaSq Kr
  rw [e]; unfold Real.goldenRatio
  have : (1 + Real.sqrt 5) / 2 - 1 = (Real.sqrt 5 - 1) / 2 := by ring
  rw [this]
  have hd : (Real.sqrt 5 - 1) / 2 + ((1:ℕ) + 1 : ℝ) * ((Real.sqrt 5 - 1) / 2) ^ (1 + 1) =
      (Real.sqrt 5 - 1) / 2 * Real.sqrt 5 := by push_cast; ring
  rw [hd]
  have hn : (Real.sqrt 5 - 1) / 2 ≠ 0 := by
    have : 2 < Real.sqrt 5 := by nlinarith
    intro h; linarith
  rw [div_eq_iff (mul_ne_zero hn hs.ne'), sub_mul, one_div, mul_comm _ (Real.sqrt 5),
    ← mul_assoc, inv_mul_cancel_left₀ hs.ne']
  ring

/-! ### 5. Asymptotics `a r n · ρ^n → B_r(ρ)/K_r`

Route (no partial fractions): `u n = a r n · ρ^n` satisfies `u (n+r+1) = ρ u (n+r) + ρ^{r+1} u n`,
an averaging recurrence (`ρ + ρ^{r+1} = 1`).  Bounds on a window of `r+1` consecutive values
propagate; each block of `r+1` steps shrinks the window's width by the factor `1 − ρ^{r+1}/2`;
and `J n = u (n+r) + ρ^{r+1} ∑_{i<r} u (n+i)` is invariant, a weighted mean of the window. -/

section Averaging

variable {r : ℕ} {u : ℕ → ℝ} {p q : ℝ}

lemma bounds_propagate (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hrec : ∀ n, u (n + r + 1) = p * u (n + r) + q * u n) {t : ℕ} {lo hi : ℝ}
    (hw : ∀ i ≤ r, lo ≤ u (t + i) ∧ u (t + i) ≤ hi) : ∀ k, lo ≤ u (t + k) ∧ u (t + k) ≤ hi := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge r k with h | h
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + r + 1 := ⟨k - r - 1, by omega⟩
      have e := hrec (t + m)
      rw [show t + m + r + 1 = t + (m + r + 1) by ring, show t + m + r = t + (m + r) by ring] at e
      obtain ⟨a1, a2⟩ := ih (m + r) (by omega)
      obtain ⟨b1, b2⟩ := ih m (by omega)
      rw [e]
      have c1 := mul_le_mul_of_nonneg_left a1 hp
      have c2 := mul_le_mul_of_nonneg_left a2 hp
      have c3 := mul_le_mul_of_nonneg_left b1 hq
      have c4 := mul_le_mul_of_nonneg_left b2 hq
      have d1 : p * lo + q * lo = lo := by rw [← add_mul, hpq, one_mul]
      have d2 : p * hi + q * hi = hi := by rw [← add_mul, hpq, one_mul]
      constructor <;> linarith
    · exact hw k h

lemma chain_upper (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hrec : ∀ n, u (n + r + 1) = p * u (n + r) + q * u n) {t : ℕ} {hi : ℝ}
    (hup : ∀ k, u (t + k) ≤ hi) :
    ∀ j, u (t + r + j) ≤ hi - p ^ j * (hi - u (t + r)) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e := hrec (t + j)
    rw [show t + j + r + 1 = t + r + (j + 1) by ring, show t + j + r = t + r + j by ring] at e
    rw [e, pow_succ]
    have c1 := mul_le_mul_of_nonneg_left ih hp
    have c2 := mul_le_mul_of_nonneg_left (hup j) hq
    have d2 : p * hi + q * hi = hi := by rw [← add_mul, hpq, one_mul]
    have : p * (hi - p ^ j * (hi - u (t + r))) = p * hi - p ^ j * p * (hi - u (t + r)) := by ring
    linarith

lemma neg_rec (hrec : ∀ n, u (n + r + 1) = p * u (n + r) + q * u n) :
    ∀ n, (fun n => -u n) (n + r + 1) = p * (fun n => -u n) (n + r) + q * (fun n => -u n) n := by
  intro n; simp only [hrec n]; ring

lemma contract (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hrec : ∀ n, u (n + r + 1) = p * u (n + r) + q * u n) {t : ℕ} {lo hi : ℝ}
    (hw : ∀ i ≤ r, lo ≤ u (t + i) ∧ u (t + i) ≤ hi) :
    ∃ lo' hi', hi' - lo' ≤ (1 - p ^ (r + 1) / 2) * (hi - lo) ∧
      ∀ i ≤ r, lo' ≤ u (t + (r + 1) + i) ∧ u (t + (r + 1) + i) ≤ hi' := by
  have hall := bounds_propagate hp hq hpq hrec hw
  have hc : 0 ≤ p ^ (r + 1) := pow_nonneg hp _
  have hpow : ∀ i ≤ r, p ^ (r + 1) ≤ p ^ (i + 1) := fun i hi =>
    pow_le_pow_of_le_one hp hp1 (by omega)
  have idx : ∀ i, t + (r + 1) + i = t + r + (i + 1) := fun i => by ring
  set x := u (t + r) with hx
  obtain ⟨hxl, hxh⟩ := hall r
  rcases le_or_gt x ((lo + hi) / 2) with h | h
  · refine ⟨lo, hi - p ^ (r + 1) * (hi - lo) / 2, by linarith, fun i hi' => ⟨?_, ?_⟩⟩
    · rw [add_assoc]; exact (hall _).1
    · rw [idx]
      have c := chain_upper hp hq hpq hrec (fun k => (hall k).2) (i + 1)
      have c1 := mul_le_mul_of_nonneg_right (hpow i hi') (show 0 ≤ hi - x by linarith)
      have c2 := mul_le_mul_of_nonneg_left (show (hi - lo) / 2 ≤ hi - x by linarith) hc
      rw [← hx] at c
      linarith
  · refine ⟨lo + p ^ (r + 1) * (hi - lo) / 2, hi, by linarith, fun i hi' => ⟨?_, ?_⟩⟩
    · rw [idx]
      have c := chain_upper (u := fun n => -u n) hp hq hpq (neg_rec hrec)
        (hi := -lo) (fun k => by simp only [neg_le_neg_iff]; exact (hall k).1) (i + 1)
      have c1 := mul_le_mul_of_nonneg_right (hpow i hi') (show 0 ≤ x - lo by linarith)
      have c2 := mul_le_mul_of_nonneg_left (show (hi - lo) / 2 ≤ x - lo by linarith) hc
      rw [← hx] at c
      linarith
    · rw [add_assoc]; exact (hall _).2

/-- The invariant `J n = u (n+r) + q ∑_{i<r} u (n+i)`. -/
def Jinv (r : ℕ) (u : ℕ → ℝ) (q : ℝ) (n : ℕ) : ℝ := u (n + r) + q * ∑ i ∈ range r, u (n + i)

lemma Jinv_const (hpq : p + q = 1) (hrec : ∀ n, u (n + r + 1) = p * u (n + r) + q * u n) :
    ∀ n, Jinv r u q n = Jinv r u q 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    unfold Jinv
    have e := hrec n
    have s1 := Finset.sum_range_succ (fun i => u (n + i)) r
    have s2 := Finset.sum_range_succ' (fun i => u (n + i)) r
    have s3 : ∑ i ∈ range r, u (n + 1 + i) = ∑ i ∈ range r, u (n + (i + 1)) :=
      Finset.sum_congr rfl (fun i _ => by rw [show n + 1 + i = n + (i + 1) by ring])
    rw [show n + 1 + r = n + r + 1 by ring, s3]
    simp only [add_zero] at s2
    have hp : p = 1 - q := by linarith
    rw [hp] at e
    linear_combination e - q * s2 + q * s1

lemma Jinv_bounds (hq : 0 ≤ q) {t : ℕ} {lo hi : ℝ}
    (hw : ∀ i ≤ r, lo ≤ u (t + i) ∧ u (t + i) ≤ hi) :
    lo * (1 + r * q) ≤ Jinv r u q t ∧ Jinv r u q t ≤ hi * (1 + r * q) := by
  unfold Jinv
  have h1 : (r : ℝ) * lo ≤ ∑ i ∈ range r, u (t + i) := by
    have := Finset.card_nsmul_le_sum (range r) (fun i => u (t + i)) lo
      (fun i hi => (hw i (by simp at hi; omega)).1)
    simpa using this
  have h2 : ∑ i ∈ range r, u (t + i) ≤ r * hi := by
    have := Finset.sum_le_card_nsmul (range r) (fun i => u (t + i)) hi
      (fun i hi => (hw i (by simp at hi; omega)).2)
    simpa using this
  have c1 := mul_le_mul_of_nonneg_left h1 hq
  have c2 := mul_le_mul_of_nonneg_left h2 hq
  obtain ⟨a1, a2⟩ := hw r le_rfl
  constructor <;> nlinarith

/-- **Averaging recurrences converge.**  If `u (n+r+1) = p u(n+r) + q u n` with `p ∈ (0,1]`,
`q ≥ 0`, `p + q = 1`, then `u n → J 0 / (1 + r q)`. -/
theorem tendsto_of_averaging (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hrec : ∀ n, u (n + r + 1) = p * u (n + r) + q * u n) :
    Filter.Tendsto u Filter.atTop (nhds (Jinv r u q 0 / (1 + r * q))) := by
  set θ := 1 - p ^ (r + 1) / 2 with hθ
  have hpr : 0 < p ^ (r + 1) := pow_pos hp _
  have hpr1 : p ^ (r + 1) ≤ 1 := pow_le_one₀ hp.le hp1
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ < 1 := by linarith
  -- initial window
  set lo0 := ∑ i ∈ range (r + 1), -|u i| with hlo0
  set hi0 := ∑ i ∈ range (r + 1), |u i| with hhi0
  have hw0 : ∀ i ≤ r, lo0 ≤ u (0 + i) ∧ u (0 + i) ≤ hi0 := by
    intro i hi
    have hm : i ∈ range (r + 1) := by simp; omega
    have b1 : |u i| ≤ hi0 := Finset.single_le_sum (f := fun i => |u i|)
      (fun j _ => abs_nonneg _) hm
    have b2 : lo0 = -hi0 := by rw [hlo0, hhi0, Finset.sum_neg_distrib]
    rw [zero_add, b2]
    exact ⟨by linarith [neg_abs_le (u i)], le_trans (le_abs_self _) b1⟩
  have hW : 0 ≤ hi0 - lo0 := by have := hw0 0 (Nat.zero_le _); linarith
  have key : ∀ k : ℕ, ∃ lo hi, hi - lo ≤ θ ^ k * (hi0 - lo0) ∧
      ∀ i ≤ r, lo ≤ u (k * (r + 1) + i) ∧ u (k * (r + 1) + i) ≤ hi := by
    intro k
    induction k with
    | zero => exact ⟨lo0, hi0, by simp, by simpa using hw0⟩
    | succ k ih =>
      obtain ⟨lo, hi, hd, hw⟩ := ih
      obtain ⟨lo', hi', hd', hw'⟩ := contract hp.le hp1 hq hpq hrec hw
      refine ⟨lo', hi', ?_, ?_⟩
      · calc hi' - lo' ≤ θ * (hi - lo) := hd'
          _ ≤ θ * (θ ^ k * (hi0 - lo0)) := mul_le_mul_of_nonneg_left hd hθ0
          _ = θ ^ (k + 1) * (hi0 - lo0) := by ring
      · intro i hi; rw [show (k + 1) * (r + 1) + i = k * (r + 1) + (r + 1) + i by ring]
        exact hw' i hi
  have hK : 0 < 1 + r * q := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (hi0 - lo0 + 1) by positivity) hθ1
  refine ⟨k * (r + 1), fun n hn => ?_⟩
  obtain ⟨lo, hi, hd, hw⟩ := key k
  obtain ⟨m, rfl⟩ : ∃ m, n = k * (r + 1) + m := ⟨n - k * (r + 1), by omega⟩
  obtain ⟨b1, b2⟩ := bounds_propagate hp.le hq hpq hrec hw m
  obtain ⟨j1, j2⟩ := Jinv_bounds hq hw
  rw [Jinv_const hpq hrec] at j1 j2
  have l1 : lo ≤ Jinv r u q 0 / (1 + r * q) := by rw [le_div_iff₀ hK]; exact j1
  have l2 : Jinv r u q 0 / (1 + r * q) ≤ hi := by rw [div_le_iff₀ hK]; exact j2
  have e1 : θ ^ k * (hi0 - lo0) < ε := by
    have := (lt_div_iff₀ (show 0 < hi0 - lo0 + 1 by linarith)).1 hk
    nlinarith [pow_nonneg hθ0 k]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Averaging

lemma sum_range_mul_pow (x : ℝ) (k : ℕ) :
    (1 - x) ^ 2 * ∑ i ∈ range k, ((i : ℝ) + 1) * x ^ i = 1 - (k + 1) * x ^ k + k * x ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

/-- `u n = a r n · ρ^n`. -/
noncomputable def uSeq (r : ℕ) (n : ℕ) : ℝ := (a r n : ℝ) * rho r ^ n

lemma uSeq_rec (r n : ℕ) :
    uSeq r (n + r + 1) = rho r * uSeq r (n + r) + rho r ^ (r + 1) * uSeq r n := by
  unfold uSeq
  rw [a_rec]; push_cast; ring

lemma Jinv_uSeq (r : ℕ) : Jinv r (uSeq r) (rho r ^ (r + 1)) 0 = (rho r ^ r)⁻¹ := by
  have h0 := rho_pos r
  have hq : 1 - rho r = rho r ^ (r + 1) := by linarith [rho_eq r]
  have hJ : Jinv r (uSeq r) (rho r ^ (r + 1)) 0 =
      (r + 1) * rho r ^ r + rho r ^ (r + 1) * ∑ i ∈ range r, ((i : ℝ) + 1) * rho r ^ i := by
    unfold Jinv uSeq
    rw [zero_add, a_of_le r r le_rfl]
    congr 2
    · push_cast; ring
    · apply Finset.sum_congr rfl; intro i hi
      rw [zero_add, a_of_le r i (by simp at hi; omega)]; push_cast; ring
  have hs := sum_range_mul_pow (rho r) r
  rw [hq] at hs
  apply eq_inv_of_mul_eq_one_left
  rw [hJ]
  set S := ∑ i ∈ range r, ((i : ℝ) + 1) * rho r ^ i
  set ρ := rho r
  have hq' : ρ ^ (r + 1) = ρ * ρ ^ r := pow_succ' ρ r
  have hne : ρ ^ (r + 1) ≠ 0 := by positivity
  -- multiply by `q = ρ^{r+1} ≠ 0`
  have hX : ρ ^ (r + 1) * (((r + 1) * ρ ^ r + ρ ^ (r + 1) * S) * ρ ^ r - 1) = 0 := by
    linear_combination ρ ^ r * hs + (ρ ^ r - ((r : ℝ) + 1) * (ρ ^ r) ^ 2) * hq
  have := (mul_eq_zero.1 hX).resolve_left hne
  linarith

/-- **Asymptotics**: `a r n · ρ^n → B_r(ρ)/K_r`. -/
theorem tendsto_a_mul_rho_pow (r : ℕ) :
    Filter.Tendsto (fun n => (a r n : ℝ) * rho r ^ n) Filter.atTop (nhds (Br r (rho r) / Kr r)) := by
  have h := tendsto_of_averaging (rho_pos r) (rho_lt_one r).le (pow_nonneg (rho_pos r).le _)
    (rho_eq r) (uSeq_rec r)
  rw [Jinv_uSeq] at h
  have hK : 1 + (r : ℝ) * rho r ^ (r + 1) = Kr r := by
    unfold Kr; have := rho_eq r; linear_combination (-1 : ℝ) * this
  rw [hK, ← Br_rho] at h
  exact h

end APEX.Blockade
