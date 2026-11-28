import OpenProblems.Prelude
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 939: sums of `r - 2` coprime `r`-powerful numbers that are `r`-powerful

Source: `formal-conjectures`, `ErdosProblems/939.lean`. We prove, with the catalogue's own
definitions (copied verbatim):

* `erdos_939.variants.seven` and `erdos_939.variants.eight` (Cambie's existence claims for
  `r = 7, 8`; category `research solved`, proofs `sorry`), by explicit witnesses;
* `erdos_939_six_infinite`: for `r = 6` there are **infinitely many** such sums (the case `r = 6`
  of `erdos_939.variants.infinite_of_six_le`, a construction recorded on erdosproblems.com);
* `erdos_939.variants.finite` (`¬ ∀ r ≥ 4, (Erdos939Sums r).Finite`) as a corollary.

All witnesses come from the binomial identity
`(X+Y)^r = (X-Y)^r + ∑_{j odd} 2·C(r,j)·X^{r-j}·Y^j` with `X = q^r`, `Y = B^r`.
-/

namespace OpenProblems.Erdos939

/-- Verbatim from formal-conjectures (`FormalConjecturesForMathlib/Data/Nat/Full.lean`). -/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

/-- Verbatim from formal-conjectures (`FormalConjecturesForMathlib/Data/Nat/Prime/Finset.lean`). -/
abbrev FinsetCoprime (S : Finset ℕ) : Prop := S.gcd id = 1

/-- Verbatim from formal-conjectures (`ErdosProblems/939.lean`), with `r.Full` spelled
`Full r` and `S.Coprime` spelled `FinsetCoprime S`. -/
def Erdos939Sums (r : ℕ) :=
    {S : Finset ℕ | S.card = r - 2 ∧ FinsetCoprime S ∧ Full r (∑ s ∈ S, s) ∧
      ∀ s ∈ S, 0 < s ∧ Full r s}

/-! ### Basic facts about `r`-full numbers -/

theorem full_pow {r k : ℕ} (m : ℕ) (hk : r ≤ k) : Full r (m ^ k) := by
  intro p hp
  have hpm : p ∣ m := (Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hp)
  exact (pow_dvd_pow p hk).trans (pow_dvd_pow_of_dvd hpm k)

theorem full_mul {r a b : ℕ} (ha : Full r a) (hb : Full r b) : Full r (a * b) := by
  intro p hp
  have hab : a * b ≠ 0 := (Nat.mem_primeFactors.1 hp).2.2
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
  rcases (Nat.prime_of_mem_primeFactors hp).dvd_mul.1 (Nat.dvd_of_mem_primeFactors hp) with h | h
  · exact (ha p (Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hp, h, ha0⟩)).mul_right b
  · exact (hb p (Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hp, h, hb0⟩)).mul_left a

/-- `c · B^r` is `r`-full as soon as every prime factor of `c` divides `B`
(here guaranteed by `c ∣ B^m`). -/
theorem full_const_mul {r c B m : ℕ} (hc : c ∣ B ^ m) : Full r (c * B ^ r) := by
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hpB : p ∣ B := by
    rcases hpr.dvd_mul.1 (Nat.dvd_of_mem_primeFactors hp) with h | h
    · exact hpr.dvd_of_dvd_pow (h.trans hc)
    · exact hpr.dvd_of_dvd_pow h
  exact (pow_dvd_pow_of_dvd hpB r).mul_left c

/-! ### The case `r = 6`: an infinite family -/

/-- The four summands for parameter `q` (with `X = q^6`, `Y = 30^6`, `D = X - Y`). -/
def S6 (q : ℕ) : Finset ℕ :=
  {(q ^ 6 - 30 ^ 6) ^ 6, 12 * (q ^ 6) ^ 5 * 30 ^ 6, 40 * (q ^ 6) ^ 3 * (30 ^ 6) ^ 3,
    12 * q ^ 6 * (30 ^ 6) ^ 5}

/-- The coprimality step for `S6`, with all quantities abstract. -/
theorem coprime_aux (q D X Y : ℕ) (hX : X = q ^ 6) (hY : Y = 30 ^ 6) (hDX : X = D + Y)
    (hcop : Nat.Coprime q 30) : Nat.Coprime D (12 * X * Y ^ 5) := by
  apply Nat.coprime_of_dvd
  intro p hp hpD hpd
  have hp30 : p ∣ 30 ∨ p ∣ q := by
    rcases hp.dvd_mul.1 hpd with h | h
    · rcases hp.dvd_mul.1 h with h | h
      · left; exact hp.dvd_of_dvd_pow (h.trans (by norm_num : 12 ∣ 30 ^ 2))
      · right; rw [hX] at h; exact hp.dvd_of_dvd_pow h
    · left; rw [hY] at h; exact hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h)
  rcases hp30 with h | h
  · have hpY : p ∣ Y := hY ▸ dvd_pow h (by norm_num)
    have hpX : p ∣ X := hDX ▸ dvd_add hpD hpY
    have hpq : p ∣ q := hp.dvd_of_dvd_pow (hX ▸ hpX)
    exact hp.one_lt.ne' (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpq h))
  · have hpX : p ∣ X := hX ▸ dvd_pow h (by norm_num)
    have hpY : p ∣ Y := (Nat.dvd_add_right hpD).1 (hDX ▸ hpX)
    have hp30 : p ∣ 30 := hp.dvd_of_dvd_pow (hY ▸ hpY)
    exact hp.one_lt.ne' (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h hp30))

theorem mem_S6 (q : ℕ) (hq : 34 ≤ q) (hodd : Odd q) (hcop : Nat.Coprime q 30) :
    S6 q ∈ Erdos939Sums 6 ∧ ∑ s ∈ S6 q, s = (q ^ 6 + 30 ^ 6) ^ 6 := by
  obtain ⟨X, hX⟩ : ∃ X, X = q ^ 6 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (30 : ℕ) ^ 6 := ⟨_, rfl⟩
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hXY : 2 * Y ≤ X := by
    have : (34 : ℕ) ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    rw [hX, hY]; norm_num at this ⊢; omega
  obtain ⟨D, hD⟩ : ∃ D, D = X - Y := ⟨_, rfl⟩
  have hDX : X = D + Y := by omega
  have hX0 : 0 < X := by omega
  have hD0 : 0 < D := by omega
  -- parity: `D` is odd
  have hDodd : Odd D := by
    have hXo : Odd X := hX ▸ hodd.pow
    have hYe : Even Y := by rw [hY]; exact (by decide : Even (30 : ℕ)).pow_of_ne_zero (by norm_num)
    rw [hD]; exact Nat.Odd.sub_even (by omega) hXo hYe
  have hDo6 : Odd (D ^ 6) := hDodd.pow
  have ev : ∀ m : ℕ, Even (12 * m) ∧ Even (40 * m) := fun m =>
    ⟨(by decide : Even (12 : ℕ)).mul_right m, (by decide : Even (40 : ℕ)).mul_right m⟩
  -- the three even summands are distinct
  have hX2 : 4 * Y ^ 2 ≤ X ^ 2 := by nlinarith
  have hbc : 40 * X ^ 3 * Y ^ 3 < 12 * X ^ 5 * Y := by
    have h1 : 40 * X ^ 3 * Y ^ 3 = (X ^ 3 * Y) * (40 * Y ^ 2) := by ring
    have h2 : 12 * X ^ 5 * Y = (X ^ 3 * Y) * (12 * X ^ 2) := by ring
    rw [h1, h2]
    apply Nat.mul_lt_mul_of_pos_left _ (Nat.pos_of_ne_zero (by simp [hX0.ne', hY0.ne', hD0.ne']))
    have : 0 < Y ^ 2 := Nat.pos_of_ne_zero (by simp [hX0.ne', hY0.ne', hD0.ne'])
    omega
  have hcd : 12 * X * Y ^ 5 < 40 * X ^ 3 * Y ^ 3 := by
    have h1 : 12 * X * Y ^ 5 = (X * Y ^ 3) * (12 * Y ^ 2) := by ring
    have h2 : 40 * X ^ 3 * Y ^ 3 = (X * Y ^ 3) * (40 * X ^ 2) := by ring
    rw [h1, h2]
    apply Nat.mul_lt_mul_of_pos_left _ (Nat.pos_of_ne_zero (by simp [hX0.ne', hY0.ne', hD0.ne']))
    have : 0 < Y ^ 2 := Nat.pos_of_ne_zero (by simp [hX0.ne', hY0.ne', hD0.ne'])
    omega
  have par : ∀ m : ℕ, ∀ c : ℕ, Even c → D ^ 6 ≠ c * m := fun m c hc h =>
    (Nat.not_even_iff_odd.2 hDo6) (h ▸ hc.mul_right m)
  have n12 : D ^ 6 ≠ 12 * X ^ 5 * Y := by
    rw [mul_assoc]; exact par _ 12 (by decide)
  have n13 : D ^ 6 ≠ 40 * X ^ 3 * Y ^ 3 := by
    rw [mul_assoc]; exact par _ 40 (by decide)
  have n14 : D ^ 6 ≠ 12 * X * Y ^ 5 := by
    rw [mul_assoc]; exact par _ 12 (by decide)
  have n23 : 12 * X ^ 5 * Y ≠ 40 * X ^ 3 * Y ^ 3 := hbc.ne'
  have n24 : 12 * X ^ 5 * Y ≠ 12 * X * Y ^ 5 := (hcd.trans hbc).ne'
  have n34 : 40 * X ^ 3 * Y ^ 3 ≠ 12 * X * Y ^ 5 := hcd.ne'
  have hnot1 : D ^ 6 ∉ ({12 * X ^ 5 * Y, 40 * X ^ 3 * Y ^ 3, 12 * X * Y ^ 5} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨n12, n13, n14⟩
  have hnot2 : 12 * X ^ 5 * Y ∉ ({40 * X ^ 3 * Y ^ 3, 12 * X * Y ^ 5} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨n23, n24⟩
  have hS : S6 q = {D ^ 6, 12 * X ^ 5 * Y, 40 * X ^ 3 * Y ^ 3, 12 * X * Y ^ 5} := by
    rw [S6, hD, hX, hY]
  have hsum : ∑ s ∈ S6 q, s = (X + Y) ^ 6 := by
    rw [hS, Finset.sum_insert hnot1, Finset.sum_insert hnot2, Finset.sum_pair n34, hDX]
    ring
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by rw [hsum, hX, hY]⟩
  · rw [hS, Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem hnot2,
      Finset.card_pair n34]
  · -- coprimality: `gcd(D^6, 12 X Y^5) = 1`
    have hcop6 : Nat.Coprime (D ^ 6) (12 * X * Y ^ 5) :=
      (coprime_aux q D X Y hX hY hDX hcop).pow_left 6
    have h1 : (S6 q).gcd id ∣ D ^ 6 := Finset.gcd_dvd (by rw [hS]; exact Finset.mem_insert_self _ _)
    have h2 : (S6 q).gcd id ∣ 12 * X * Y ^ 5 := Finset.gcd_dvd (by
      rw [hS]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))))
    exact Nat.eq_one_of_dvd_one (hcop6 ▸ Nat.dvd_gcd h1 h2)
  · rw [hsum]; exact full_pow _ le_rfl
  · rw [hS]
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h | h <;> rw [h]
    · exact ⟨Nat.pos_of_ne_zero (by simp [hX0.ne', hY0.ne', hD0.ne']), full_pow _ le_rfl⟩
    · refine ⟨Nat.pos_of_ne_zero (by simp [hX0.ne', hY0.ne', hD0.ne']), ?_⟩
      have : 12 * X ^ 5 * Y = (12 * 30 ^ 6) * q ^ 30 := by rw [hX, hY]; ring
      rw [this]; exact full_mul (full_const_mul (m := 2) (by norm_num)) (full_pow _ (by norm_num))
    · refine ⟨Nat.pos_of_ne_zero (by simp [hX0.ne', hY0.ne', hD0.ne']), ?_⟩
      have : 40 * X ^ 3 * Y ^ 3 = ((40 * 30 ^ 6) * 30 ^ 12) * q ^ 18 := by rw [hX, hY]; ring
      rw [this]
      exact full_mul (full_mul (full_const_mul (m := 3) (by norm_num)) (full_pow _ (by norm_num)))
        (full_pow _ (by norm_num))
    · refine ⟨Nat.pos_of_ne_zero (by simp [hX0.ne', hY0.ne', hD0.ne']), ?_⟩
      have : 12 * X * Y ^ 5 = ((12 * 30 ^ 6) * 30 ^ 24) * q ^ 6 := by rw [hX, hY]; ring
      rw [this]
      exact full_mul (full_mul (full_const_mul (m := 2) (by norm_num)) (full_pow _ (by norm_num)))
        (full_pow _ le_rfl)

/-- **Case `r = 6` of `erdos_939.variants.infinite_of_six_le`**: infinitely many sums of four
coprime 6-powerful numbers are 6-powerful. The family is `q = 30 t + 61`. -/
theorem erdos_939_six_infinite : (Erdos939Sums 6).Infinite := by
  have hc : ∀ t : ℕ, Nat.Coprime (30 * t + 61) 30 := fun t => by
    rw [Nat.Coprime, show 30 * t + 61 = 1 + 30 * (t + 2) by ring, Nat.gcd_add_mul_left_left]
    norm_num
  have hmem : ∀ t : ℕ, S6 (30 * t + 61) ∈ Erdos939Sums 6 := fun t =>
    (mem_S6 _ (by omega) ⟨15 * t + 30, by ring⟩ (hc t)).1
  refine Set.infinite_of_injective_forall_mem (f := fun t => S6 (30 * t + 61)) ?_ hmem
  intro t u htu
  have h1 := (mem_S6 (30 * t + 61) (by omega) ⟨15 * t + 30, by ring⟩ (hc t)).2
  have h2 := (mem_S6 (30 * u + 61) (by omega) ⟨15 * u + 30, by ring⟩ (hc u)).2
  have heq : ((30 * t + 61) ^ 6 + 30 ^ 6) ^ 6 = ((30 * u + 61) ^ 6 + 30 ^ 6) ^ 6 := by
    rw [← h1, ← h2]; exact congrArg (fun S => ∑ s ∈ S, s) htu
  have := Nat.pow_left_injective (by norm_num : (6 : ℕ) ≠ 0) heq
  have := Nat.add_right_cancel this
  have := Nat.pow_left_injective (by norm_num : (6 : ℕ) ≠ 0) this
  omega

/-- `erdos_939.variants.finite`: the finiteness question has a negative answer. -/
theorem erdos_939_not_finite : ¬ ∀ r ≥ 4, (Erdos939Sums r).Finite := fun h =>
  erdos_939_six_infinite (h 6 (by norm_num))

/-! ### The cases `r = 7` and `r = 8` (Cambie): explicit witnesses -/

/-- Witness for `r = 7`: `X = 211^7`, `Y = 210^7`. -/
def S7 : Finset ℕ :=
  {(211 ^ 7 - 210 ^ 7) ^ 7, 14 * (211 ^ 7) ^ 6 * 210 ^ 7, 70 * (211 ^ 7) ^ 4 * (210 ^ 7) ^ 3,
    42 * (211 ^ 7) ^ 2 * (210 ^ 7) ^ 5, 2 * (210 ^ 7) ^ 7}

/-- `erdos_939.variants.seven`. -/
theorem erdos_939_seven : (Erdos939Sums 7).Nonempty := by
  refine ⟨S7, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · have : ∑ s ∈ S7, s = (211 ^ 7 + 210 ^ 7) ^ 7 := by decide +kernel
    rw [this]; exact full_pow _ le_rfl
  · intro s hs
    simp only [S7, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by norm_num, full_pow _ le_rfl⟩
    · refine ⟨by positivity, ?_⟩
      rw [show 14 * (211 ^ 7) ^ 6 * 210 ^ 7 = (14 * 210 ^ 7) * 211 ^ 42 by ring]
      exact full_mul (full_const_mul (m := 1) (by norm_num)) (full_pow _ (by norm_num))
    · refine ⟨by positivity, ?_⟩
      rw [show 70 * (211 ^ 7) ^ 4 * (210 ^ 7) ^ 3 = ((70 * 210 ^ 7) * 210 ^ 14) * 211 ^ 28 by ring]
      exact full_mul (full_mul (full_const_mul (m := 1) (by norm_num)) (full_pow _ (by norm_num)))
        (full_pow _ (by norm_num))
    · refine ⟨by positivity, ?_⟩
      rw [show 42 * (211 ^ 7) ^ 2 * (210 ^ 7) ^ 5 = ((42 * 210 ^ 7) * 210 ^ 28) * 211 ^ 14 by ring]
      exact full_mul (full_mul (full_const_mul (m := 1) (by norm_num)) (full_pow _ (by norm_num)))
        (full_pow _ (by norm_num))
    · refine ⟨by positivity, ?_⟩
      rw [show 2 * (210 ^ 7) ^ 7 = (2 * 210 ^ 7) * 210 ^ 42 by ring]
      exact full_mul (full_const_mul (m := 1) (by norm_num)) (full_pow _ (by norm_num))

/-- Witness for `r = 8`: `X = 15^8`, `Y = 14^8`; the `X^5 Y^3` term `112 = 14 + 98` is split. -/
def S8 : Finset ℕ :=
  {(15 ^ 8 - 14 ^ 8) ^ 8, 16 * (15 ^ 8) ^ 7 * 14 ^ 8, 14 * (15 ^ 8) ^ 5 * (14 ^ 8) ^ 3,
    98 * (15 ^ 8) ^ 5 * (14 ^ 8) ^ 3, 112 * (15 ^ 8) ^ 3 * (14 ^ 8) ^ 5, 16 * 15 ^ 8 * (14 ^ 8) ^ 7}

/-- `erdos_939.variants.eight`. -/
theorem erdos_939_eight : (Erdos939Sums 8).Nonempty := by
  refine ⟨S8, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · have : ∑ s ∈ S8, s = (15 ^ 8 + 14 ^ 8) ^ 8 := by decide +kernel
    rw [this]; exact full_pow _ le_rfl
  · intro s hs
    simp only [S8, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by norm_num, full_pow _ le_rfl⟩
    · refine ⟨by positivity, ?_⟩
      rw [show 16 * (15 ^ 8) ^ 7 * 14 ^ 8 = (16 * 14 ^ 8) * 15 ^ 56 by ring]
      exact full_mul (full_const_mul (m := 4) (by norm_num)) (full_pow _ (by norm_num))
    · refine ⟨by positivity, ?_⟩
      rw [show 14 * (15 ^ 8) ^ 5 * (14 ^ 8) ^ 3 = ((14 * 14 ^ 8) * 14 ^ 16) * 15 ^ 40 by ring]
      exact full_mul (full_mul (full_const_mul (m := 1) (by norm_num)) (full_pow _ (by norm_num)))
        (full_pow _ (by norm_num))
    · refine ⟨by positivity, ?_⟩
      rw [show 98 * (15 ^ 8) ^ 5 * (14 ^ 8) ^ 3 = ((98 * 14 ^ 8) * 14 ^ 16) * 15 ^ 40 by ring]
      exact full_mul (full_mul (full_const_mul (m := 2) (by norm_num)) (full_pow _ (by norm_num)))
        (full_pow _ (by norm_num))
    · refine ⟨by positivity, ?_⟩
      rw [show 112 * (15 ^ 8) ^ 3 * (14 ^ 8) ^ 5 = ((112 * 14 ^ 8) * 14 ^ 32) * 15 ^ 24 by ring]
      exact full_mul (full_mul (full_const_mul (m := 4) (by norm_num)) (full_pow _ (by norm_num)))
        (full_pow _ (by norm_num))
    · refine ⟨by positivity, ?_⟩
      rw [show 16 * 15 ^ 8 * (14 ^ 8) ^ 7 = ((16 * 14 ^ 8) * 14 ^ 48) * 15 ^ 8 by ring]
      exact full_mul (full_mul (full_const_mul (m := 4) (by norm_num)) (full_pow _ (by norm_num)))
        (full_pow _ le_rfl)

end OpenProblems.Erdos939
