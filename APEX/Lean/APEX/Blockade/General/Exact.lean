import APEX.Blockade.General.Degree
import APEX.PXP.MaskDP
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

/-!
# Range-`r` blockade, all even moments: values of `Lc m` and exactness of the denominator

Notation: `S_{m,r} = ∑ₙ Tr A_{n,r}^{2m} zⁿ`, `D_r = 1 − z − z^{r+1}`, and `P` the numerator with
`S_{m,r} · D_r^{m+1} = P` (`Rational.lean`, `Degree.lean`).

**Part 1 (kernel values of the leading coefficient).**  `Lc_eq_LcQ` proves `Lc m = LcQ m` for
`m ≥ 1`, where `LcQ` is a bit-mask recursion (two-flip trajectories as masks `< 2^{2m}`,
candidate lists stored in a binary tree).  The Lean kernel then evaluates (`decide +kernel`):
`Lc_one : Lc 1 = 2`, `Lc_two : Lc 2 = -4`, `Lc_three : Lc 3 = 36`, `Lc_four : Lc 4 = -568`,
`Lc_five : Lc 5 = 14560` (the last split into 14 partial sums over the first trajectory).

**Part 2 (exact denominator).**  `numerator_isCoprime`: for `r, m ≥ 1` and any `P ∈ ℤ[z]` with
`S_{m,r} · D_r^{m+1} = P`, `P` and `D_r` are coprime in `ℚ[z]` (from
`P ≡ (2m)! z^{(r+1)m−r} (mod D_r)`).  `exact_denominator`: if `S_{m,r} · D_r^j = Q` for some
`Q ∈ ℚ[z]` then `j ≥ m + 1`; `no_cancellation`: `S_{m,r} · D_r^m` is not a polynomial.  This holds
for every `r ≥ 1`, including `r ≡ 4 (mod 6)` where `D_r` is reducible.

**Part 3.**  `cyc6_dvd_D_iff`: `z² − z + 1 ∣ D_r` in `ℤ[z]` iff `r ≡ 4 (mod 6)`.
-/

namespace APEX.Blockade.General

open Finset
open APEX.PXP (Traj flips)
open APEX.PXP.MaskDP (dec decF BT)

/-! ## Part 1: a kernel-evaluable form of the leading coefficient `Lc m` -/

/-- Masks `c < 2^k` encoding trajectories with exactly two flips. -/
def L2 (k : ℕ) : List ℕ :=
  (List.range (2 ^ k)).filter (fun c => (decF k (APEX.PXP.MaskDP.fl k c)).card == 2)

/-- Two-flip masks whose flip set lies inside the mask `S`. -/
def cand2 (k S : ℕ) : List ℕ :=
  (L2 k).filter (fun c => APEX.PXP.MaskDP.fl k c &&& S == APEX.PXP.MaskDP.fl k c)

/-- The table `S ↦ cand2 k S`, as a binary tree of depth `k`. -/
def C2T (k : ℕ) : BT (List ℕ) := BT.build k (cand2 k)

/-- Bit-mask version of `τ`, looking candidates up in the table `T`. -/
def τQ (k : ℕ) (T : BT (List ℕ)) : ℕ → ℕ → ℕ → ℤ
  | 0, _, f => if f == 0 then 1 else 0
  | g + 1, b, f => if f == 0 then 1 else
      -((T.get f).map fun c => if c &&& b == 0 then
          τQ k T g c (f ^^^ APEX.PXP.MaskDP.fl k c) else 0).sum

/-- Contribution of a list of first trajectories to the bit-mask leading coefficient. -/
def LcPart (m : ℕ) (l : List ℕ) : ℤ :=
  (l.map fun c => τQ (2 * m) (C2T (2 * m)) (m - 1) c
    ((2 ^ (2 * m) - 1) ^^^ APEX.PXP.MaskDP.fl (2 * m) c)).sum

/-- Bit-mask leading coefficient. -/
def LcQ (m : ℕ) : ℤ := LcPart m (L2 (2 * m))

lemma LcPart_append (m : ℕ) (l l' : List ℕ) : LcPart m (l ++ l') = LcPart m l + LcPart m l' := by
  simp [LcPart]

lemma sum_filter_range_int (p : ℕ → Bool) (h : ℕ → ℤ) (N : ℕ) :
    (((List.range N).filter p).map h).sum = ∑ c ∈ range N, if p c then h c else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    by_cases hp : p N <;> simp [hp]

lemma sum_act_eq {k : ℕ} (φ : Traj k → ℤ) (hφ : ∀ β, flips β = ∅ → φ β = 0) :
    ∑ β ∈ act k, φ β = ∑ c ∈ range (2 ^ k), φ (dec k c) := by
  rw [← APEX.PXP.MaskDP.sum_traj]
  refine sum_subset (subset_univ _) (fun β _ hβ => hφ β ?_)
  simp only [act, mem_filter, mem_univ, true_and] at hβ
  exact not_nonempty_iff_eq_empty.1 hβ

lemma C2T_get {k S : ℕ} (hS : S < 2 ^ k) : (C2T k).get S = cand2 k S :=
  BT.get_build _ _ _ hS

lemma disjoint_occ_dec {k b c : ℕ} (hc : c < 2 ^ k) (hb : b < 2 ^ k) :
    Disjoint (occ (dec k c)) (occ (dec k b)) ↔ c &&& b = 0 := by
  rw [← compat_iff, APEX.PXP.MaskDP.compat_dec_iff hc hb]

theorem τ_eq_τQ {k : ℕ} : ∀ (g b f : ℕ), b < 2 ^ k → f < 2 ^ k →
    τ g (dec k b) (decF k f) = τQ k (C2T k) g b f
  | 0, b, f, _, hf => by
    simp only [τ, τQ, APEX.PXP.MaskDP.decF_eq_empty_iff hf, beq_iff_eq]
  | g + 1, b, f, hb, hf => by
    simp only [τ, τQ, APEX.PXP.MaskDP.decF_eq_empty_iff hf, beq_iff_eq]
    split_ifs with h0
    · rfl
    congr 1
    rw [C2T_get hf, cand2, L2, List.filter_filter, sum_filter_range_int]
    rw [sum_act_eq]
    · refine sum_congr rfl (fun c hc => ?_)
      have hc' : c < 2 ^ k := mem_range.1 hc
      have hfl := APEX.PXP.MaskDP.fl_lt hc'
      rw [APEX.PXP.MaskDP.flips_dec hc']
      simp only [APEX.PXP.MaskDP.decF_subset_iff hfl hf, disjoint_occ_dec hc' hb]
      by_cases h1 : (decF k (APEX.PXP.MaskDP.fl k c)).card = 2
      · by_cases h2 : APEX.PXP.MaskDP.fl k c &&& f = APEX.PXP.MaskDP.fl k c
        · rw [APEX.PXP.MaskDP.decF_sdiff h2,
            τ_eq_τQ g c _ hc' (Nat.xor_lt_two_pow hf hfl)]
          simp [h1, h2]
        · simp [h1, h2]
      · simp [h1]
    · intro β hβ
      rw [hβ]; simp

theorem Lc_eq_LcQ {m : ℕ} (hm : 1 ≤ m) : Lc m = LcQ m := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have hF : 2 ^ (2 * m) - 1 < 2 ^ (2 * m) := Nat.sub_lt (by positivity) one_pos
  rw [Lc, cΦ, LcQ, LcPart, L2, sum_filter_range_int, sum_act_eq]
  · refine sum_congr rfl (fun c hc => ?_)
    have hc' : c < 2 ^ (2 * m) := mem_range.1 hc
    have hfl := APEX.PXP.MaskDP.fl_lt hc'
    have hsub : APEX.PXP.MaskDP.fl (2 * m) c &&& (2 ^ (2 * m) - 1) = APEX.PXP.MaskDP.fl (2 * m) c := by
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hfl]
    simp only [subset_univ, ↓reduceIte, cT]
    rw [ APEX.PXP.MaskDP.flips_dec hc',
      ← APEX.PXP.MaskDP.decF_full (2 * m), APEX.PXP.MaskDP.decF_sdiff hsub,
      τ_eq_τQ _ c _ hc' (Nat.xor_lt_two_pow hF hfl)]
    by_cases h1 : (decF (2 * m) (APEX.PXP.MaskDP.fl (2 * m) c)).card = 2 <;> simp [h1]
  · intro β hβ
    simp only [subset_univ, ↓reduceIte, cT]
    rw [ hβ]; simp

theorem Lc_one : Lc 1 = 2 := by rw [Lc_eq_LcQ le_rfl]; decide +kernel
theorem Lc_two : Lc 2 = -4 := by rw [Lc_eq_LcQ (by norm_num)]; decide +kernel
theorem Lc_three : Lc 3 = 36 := by rw [Lc_eq_LcQ (by norm_num)]; decide +kernel
theorem Lc_four : Lc 4 = -568 := by rw [Lc_eq_LcQ (by norm_num)]; decide +kernel

/-! ### `Lc 5`: the 90 two-flip first trajectories, split into 14 kernel checks -/

lemma L2_ten : L2 10 = [1, 2, 3, 4, 6, 7, 8, 12, 14, 15, 16, 24, 28, 30, 31, 32, 48, 56, 60, 62, 63, 64, 96, 112, 120, 124, 126, 127, 128, 192, 224, 240, 248, 252, 254, 255, 256, 384, 448, 480, 496, 504, 508, 510, 511, 512, 513, 515, 519, 527, 543, 575, 639, 767, 768, 769, 771, 775, 783, 799, 831, 895, 896, 897, 899, 903, 911, 927, 959, 960, 961, 963, 967, 975, 991, 992, 993, 995, 999, 1007, 1008, 1009, 1011, 1015, 1016, 1017, 1019, 1020, 1021, 1022] := by decide +kernel

lemma LcPart5_0 : LcPart 5 [1, 2, 3] = 1168 := by decide +kernel
lemma LcPart5_1 : LcPart 5 [4, 6, 7] = 1026 := by decide +kernel
lemma LcPart5_2 : LcPart 5 [8, 12, 14] = 1026 := by decide +kernel
lemma LcPart5_3 : LcPart 5 [15, 16, 24] = 955 := by decide +kernel
lemma LcPart5_4 : LcPart 5 [28, 30, 31, 32] = 1016 := by decide +kernel
lemma LcPart5_5 : LcPart 5 [48, 56, 60, 62, 63] = 1017 := by decide +kernel
lemma LcPart5_6 : LcPart 5 [64, 96, 112] = 1026 := by decide +kernel
lemma LcPart5_7 : LcPart 5 [120, 124, 126, 127, 128, 192] = 1185 := by decide +kernel
lemma LcPart5_8 : LcPart 5 [224, 240, 248, 252, 254, 255, 256] = 1114 := by decide +kernel
lemma LcPart5_9 : LcPart 5 [384, 448, 480, 496, 504, 508, 510, 511] = 1043 := by decide +kernel
lemma LcPart5_10 : LcPart 5 [512, 513, 515] = 1026 := by decide +kernel
lemma LcPart5_11 : LcPart 5 [519, 527, 543, 575, 639, 767, 768, 769] = 1043 := by decide +kernel
lemma LcPart5_12 : LcPart 5 [771, 775, 783, 799, 831, 895, 896, 897, 899, 903, 911, 927, 959] = 1131 := by decide +kernel
lemma LcPart5_13 : LcPart 5 [960, 961, 963, 967, 975, 991, 992, 993, 995, 999, 1007, 1008, 1009, 1011, 1015, 1016, 1017, 1019, 1020, 1021, 1022] = 784 := by decide +kernel

theorem Lc_five : Lc 5 = 14560 := by
  rw [Lc_eq_LcQ (by norm_num), LcQ, show 2 * 5 = 10 from rfl, L2_ten,
    show [1, 2, 3, 4, 6, 7, 8, 12, 14, 15, 16, 24, 28, 30, 31, 32, 48, 56, 60, 62, 63, 64, 96, 112, 120, 124, 126, 127, 128, 192, 224, 240, 248, 252, 254, 255, 256, 384, 448, 480, 496, 504, 508, 510, 511, 512, 513, 515, 519, 527, 543, 575, 639, 767, 768, 769, 771, 775, 783, 799, 831, 895, 896, 897, 899, 903, 911, 927, 959, 960, 961, 963, 967, 975, 991, 992, 993, 995, 999, 1007, 1008, 1009, 1011, 1015, 1016, 1017, 1019, 1020, 1021, 1022] =
      [1, 2, 3] ++ [4, 6, 7] ++ [8, 12, 14] ++ [15, 16, 24] ++ [28, 30, 31, 32] ++ [48, 56, 60, 62, 63] ++ [64, 96, 112] ++ [120, 124, 126, 127, 128, 192] ++ [224, 240, 248, 252, 254, 255, 256] ++ [384, 448, 480, 496, 504, 508, 510, 511] ++ [512, 513, 515] ++ [519, 527, 543, 575, 639, 767, 768, 769] ++ [771, 775, 783, 799, 831, 895, 896, 897, 899, 903, 911, 927, 959] ++ [960, 961, 963, 967, 975, 991, 992, 993, 995, 999, 1007, 1008, 1009, 1011, 1015, 1016, 1017, 1019, 1020, 1021, 1022] from rfl]
  simp only [LcPart_append, LcPart5_0, LcPart5_1, LcPart5_2, LcPart5_3, LcPart5_4, LcPart5_5, LcPart5_6, LcPart5_7, LcPart5_8, LcPart5_9, LcPart5_10, LcPart5_11, LcPart5_12, LcPart5_13]
  norm_num

/-! ## Part 2: the denominator `D_r^{m+1}` is exact -/

section Denominator

open Polynomial


/-- `X` and `D_r = 1 − X − X^{r+1}` are coprime over any commutative ring. -/
lemma isCoprime_X_D {R : Type*} [CommRing R] (r : ℕ) :
    IsCoprime (X : R[X]) (1 - X - X ^ (r + 1)) :=
  ⟨1 + X ^ r, 1, by ring⟩

lemma map_Dpol (r : ℕ) :
    (Dpol r).map (Int.castRingHom ℚ) = (1 - X - X ^ (r + 1) : ℚ[X]) := by
  simp only [Dpol, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, Polynomial.map_pow]

lemma natDegree_DQ {r : ℕ} (hr : 1 ≤ r) : (1 - X - X ^ (r + 1) : ℚ[X]).natDegree = r + 1 := by
  have h1 : (1 - X : ℚ[X]).natDegree < (X ^ (r + 1) : ℚ[X]).natDegree := by
    rw [natDegree_X_pow]
    refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
    simp; omega
  rw [natDegree_sub_eq_right_of_natDegree_lt h1, natDegree_X_pow]

lemma not_isUnit_DQ {r : ℕ} (hr : 1 ≤ r) : ¬ IsUnit (1 - X - X ^ (r + 1) : ℚ[X]) := by
  intro h
  have := natDegree_eq_zero_of_isUnit h
  rw [natDegree_DQ hr] at this
  omega

/-- **Coprimality of numerator and denominator.**  For `r, m ≥ 1`, the numerator `P ∈ ℤ[X]` of
`(∑ₙ Tr A_{n,r}^{2m} zⁿ)·D_r^{m+1} = P` is coprime to `D_r` in `ℚ[X]`. -/
theorem numerator_isCoprime {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (P : Polynomial ℤ)
    (hP : PowerSeries.mk (fun n => Mk (2 * m) r n) *
      (1 - PowerSeries.X - PowerSeries.X ^ (r + 1)) ^ (m + 1) = (P : PowerSeries ℤ)) :
    IsCoprime (P.map (Int.castRingHom ℚ)) ((Dpol r).map (Int.castRingHom ℚ)) := by
  obtain ⟨P', q, -, hS', hq⟩ := moment_residue hr hm
  have hPP : P = P' := Polynomial.coe_inj.1 (hP.symm.trans hS')
  subst hPP
  rw [map_Dpol, hq]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one]
  have hunit : ∀ (c : ℚ) (p : ℚ[X]), c ≠ 0 → IsCoprime (Polynomial.C c) p := fun c p hc =>
    ⟨Polynomial.C c⁻¹, 0, by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1, zero_mul, add_zero]⟩
  refine IsCoprime.add_mul_left_left
    (IsCoprime.mul_left (hunit _ _ ?_) ((isCoprime_X_D r).pow_left)) _
  simp [Nat.factorial_ne_zero]

/-- The series `∑ₙ Tr A_{n,r}^{2m} zⁿ` with rational coefficients. -/
noncomputable def serQ (m r : ℕ) : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk (fun n => Mk (2 * m) r n))

/-- **Exact denominator.**  If `serQ m r · D_r^j` is a polynomial `Q ∈ ℚ[X]`, then `j ≥ m+1`. -/
theorem exact_denominator {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {j : ℕ} {Q : ℚ[X]}
    (hQ : serQ m r * (1 - PowerSeries.X - PowerSeries.X ^ (r + 1)) ^ j = (Q : PowerSeries ℚ)) :
    m + 1 ≤ j := by
  by_contra hj
  rw [not_le] at hj
  obtain ⟨P, -, hP⟩ := moment_rational hr hm
  have hcop := numerator_isCoprime hr hm P hP
  have hPQ := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hP
  rw [← Polynomial.polynomial_map_coe] at hPQ
  simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.map_X] at hPQ
  have hsplit : m + 1 = j + (m + 1 - j) := by omega
  rw [hsplit, pow_add, ← mul_assoc] at hPQ
  change serQ m r * _ * _ = _ at hPQ
  rw [hQ] at hPQ
  have hD : ((1 - X - X ^ (r + 1) : ℚ[X]) : PowerSeries ℚ) =
      1 - PowerSeries.X - PowerSeries.X ^ (r + 1) := by simp
  rw [← hD, ← Polynomial.coe_pow, ← Polynomial.coe_mul, Polynomial.coe_inj] at hPQ
  have hdvd : (1 - X - X ^ (r + 1) : ℚ[X]) ∣ P.map (Int.castRingHom ℚ) := by
    rw [← hPQ]
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
  rw [map_Dpol] at hcop
  exact not_isUnit_DQ hr (hcop.isUnit_of_dvd' hdvd dvd_rfl)

/-- `moment_exact` together with coprimality: the numerator has exact degree
`(2r+1)(m−1)+1`, leading coefficient `Lc m`, and is coprime to `D_r` over `ℚ`. -/
theorem moment_exact_coprime {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    ∃ P : Polynomial ℤ, P.natDegree = (2 * r + 1) * (m - 1) + 1 ∧
      PowerSeries.mk (fun n => Mk (2 * m) r n) *
        (1 - PowerSeries.X - PowerSeries.X ^ (r + 1)) ^ (m + 1) = (P : PowerSeries ℤ) ∧
      P.leadingCoeff = Lc m ∧
      IsCoprime (P.map (Int.castRingHom ℚ)) ((Dpol r).map (Int.castRingHom ℚ)) := by
  obtain ⟨P, h1, h2, h3⟩ := moment_exact hr hm
  exact ⟨P, h1, h2, h3, numerator_isCoprime hr hm P h2⟩

/-- **No cancellation.**  `serQ m r · D_r^m` is not a polynomial (for every `r ≥ 1`, including
`r ≡ 4 (mod 6)` where `D_r` is reducible). -/
theorem no_cancellation {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    ¬ ∃ Q : ℚ[X],
      serQ m r * (1 - PowerSeries.X - PowerSeries.X ^ (r + 1)) ^ m = (Q : PowerSeries ℚ) := by
  rintro ⟨Q, hQ⟩
  have := exact_denominator hr hm hQ
  omega

/-! ## Part 3: the factor `X² − X + 1` of `D_r` for `r ≡ 4 (mod 6)` -/

lemma cyc6_dvd_pow6 (t : ℕ) : (X ^ 2 - X + 1 : ℤ[X]) ∣ (X ^ 6) ^ t - 1 := by
  have h1 : (X ^ 2 - X + 1 : ℤ[X]) ∣ X ^ 6 - 1 := ⟨(X + 1) * (X ^ 3 - 1), by ring⟩
  exact h1.trans (by simpa using sub_dvd_pow_sub_pow (X ^ 6 : ℤ[X]) 1 t)

theorem cyc6_dvd_D {r : ℕ} (h : r % 6 = 4) :
    (X ^ 2 - X + 1 : ℤ[X]) ∣ 1 - X - X ^ (r + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = 6 * t + 4 := ⟨r / 6, by omega⟩
  obtain ⟨u, hu⟩ := cyc6_dvd_pow6 t
  refine ⟨-(X ^ 3 + X ^ 2 - 1) - X ^ 5 * u, ?_⟩
  have : (X : ℤ[X]) ^ (6 * t + 4 + 1) = X ^ 5 * ((X ^ 6) ^ t - 1) + X ^ 5 := by
    rw [← pow_mul]; ring
  rw [this, hu]
  ring

lemma natDegree_cyc6 : (X ^ 2 - X + 1 : ℤ[X]).natDegree = 2 := by compute_degree!

lemma eq_zero_of_cyc6_dvd {b : ℤ[X]} (h : (X ^ 2 - X + 1 : ℤ[X]) ∣ b) (hb : b.natDegree ≤ 1) :
    b = 0 := by
  obtain ⟨q, rfl⟩ := h
  by_contra hne
  have hq : q ≠ 0 := by rintro rfl; simp at hne
  have h0 : (X ^ 2 - X + 1 : ℤ[X]) ≠ 0 := by
    intro h; have := natDegree_cyc6; rw [h] at this; simp at this
  rw [natDegree_mul h0 hq, natDegree_cyc6] at hb
  omega

/-- `X² − X + 1` divides `D_r = 1 − X − X^{r+1}` in `ℤ[X]` exactly when `r ≡ 4 (mod 6)`. -/
theorem cyc6_dvd_D_iff (r : ℕ) :
    (X ^ 2 - X + 1 : ℤ[X]) ∣ 1 - X - X ^ (r + 1) ↔ r % 6 = 4 := by
  refine ⟨fun h => ?_, cyc6_dvd_D⟩
  obtain ⟨t, j, hj, hr⟩ : ∃ t j, j < 6 ∧ r + 1 = 6 * t + j := ⟨(r + 1) / 6, (r + 1) % 6,
    Nat.mod_lt _ (by norm_num), (Nat.div_add_mod _ _).symm⟩
  have hsplit : (1 - X - X ^ (r + 1) : ℤ[X]) =
      (1 - X - X ^ j) - X ^ j * ((X ^ 6) ^ t - 1) := by
    rw [hr, ← pow_mul]; ring
  rw [hsplit] at h
  have hj' : (X ^ 2 - X + 1 : ℤ[X]) ∣ 1 - X - X ^ j :=
    (dvd_sub_left (Dvd.dvd.mul_left (cyc6_dvd_pow6 t) _)).1 h
  have key : ∀ a b : ℤ[X], (X ^ 2 - X + 1 : ℤ[X]) ∣ (X ^ 2 - X + 1) * a + b →
      b.natDegree ≤ 1 → b = 0 := fun a b h hb =>
    eq_zero_of_cyc6_dvd ((dvd_add_right (dvd_mul_right _ _)).1 h) hb
  interval_cases j
  · exfalso
    have := key 0 (-X) (by convert hj' using 1; ring) (by compute_degree!)
    have := congrArg (eval 1) this; simp at this
  · exfalso
    have := key 0 (1 - 2 * X) (by convert hj' using 1; ring) (by compute_degree!)
    have := congrArg (eval 1) this; norm_num at this
  · exfalso
    have := key (-1) (2 - 2 * X) (by convert hj' using 1; ring) (by compute_degree!)
    have := congrArg (eval 0) this; simp at this
  · exfalso
    have := key (-(X + 1)) (2 - X) (by convert hj' using 1; ring) (by compute_degree!)
    have := congrArg (eval 0) this; simp at this
  · exfalso
    have := key (-(X * (X + 1))) 1 (by convert hj' using 1; ring) (by compute_degree!)
    simp at this
  · omega

end Denominator

end APEX.Blockade.General

