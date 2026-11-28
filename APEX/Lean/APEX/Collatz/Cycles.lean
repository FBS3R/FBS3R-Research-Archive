import APEX.Collatz.StoppingTime

/-!
# Collatz: finite-range constraints on nontrivial cycles

Everything here concerns the standard Collatz map `C` of `APEX.Collatz.StoppingTime`.

**Definitions.**
* `IsNontrivialCycle n p`: `1 ≤ n`, `1 ≤ p`, `C^[p] n = n` and `n ∉ {1, 2, 4}`.
* `orbitMin n`: the least value of the forward orbit `{C^[j] n | j ∈ ℕ}` (via `Nat.find`).

**Proved (all kernel-checked, no `native_decide`).**
1. `cycleMin_spec`: for a nontrivial cycle through `n`, `m = orbitMin n` lies on the cycle
   (`C^[a] n = m`, `C^[k] m = n`, `C^[p] m = m`), `2 ≤ m`, `m ≤ C^[j] m` for every `j`, and
   hence `¬ HasStoppingTime m`.
2. `small_drop` (kernel computation, 64 chunks of 16384 values, `decide +kernel`):
   every `n` with `2 ≤ n ≤ 2^20` has some `1 ≤ i ≤ 400` with `C^[i] n < n`
   (via a fuel-bounded `Tt` checker, fuel `200`; the actual maximum `Tt` stopping time on this
   range is `183`).  Consequences, by strong induction: `reaches_one_le_2pow20`
   (`1 ≤ n ≤ 2^20 → ∃ k, C^[k] n = 1`) and `stoppingTime_le_2pow20`
   (`1 ≤ n ≤ 2^20 → n = 1 ∨ HasStoppingTime n`).
3. `nontrivial_cycle_constraints`: if a nontrivial cycle exists, its minimal element `m`
   satisfies `2^20 < m` and `m % 2^18 ∈ uncertified 18` (one of the `7495` residue classes
   mod `2^18` not certified by `certB`).
4. `no_small_nontrivial_cycle`: no nontrivial cycle contains any `n ≤ 2^20`; equivalently
   every element of a nontrivial cycle is `> 2^20`.

**Caveat (KNOWN_RESULT style).** This is NOT a proof of the Collatz conjecture, nor of the
non-existence of nontrivial cycles.  It is a finite-range constraint: the literature verifies
convergence for all `n` up to about `2^71` and much stronger lower bounds on cycle lengths
(Simons–de Weger, Hercher).  Here only `n ≤ 2^20` is checked, plus the mod-`2^18` residue
restriction for the cycle minimum.
-/

namespace APEX.Collatz

/-! ### Basic facts on `C` -/

lemma C_pos {n : ℕ} (h : 1 ≤ n) : 1 ≤ C n := by
  unfold C; split <;> omega

lemma C_iterate_pos {n : ℕ} (h : 1 ≤ n) : ∀ j, 1 ≤ C^[j] n := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih => rw [Function.iterate_succ_apply']; exact C_pos ih

lemma C_lt_of_even {n : ℕ} (h2 : 2 ≤ n) (he : n % 2 = 0) : C n < n := by
  unfold C; simp only [he, ↓reduceIte]; omega

lemma C_iterate_one (k : ℕ) : C^[k] 1 = 1 ∨ C^[k] 1 = 2 ∨ C^[k] 1 = 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h <;> rw [h] <;> decide

lemma C_iterate_mul_period {n p : ℕ} (h : C^[p] n = n) : ∀ t, C^[p * t] n = n := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, Function.iterate_add_apply, h, ih]

/-! ### Nontrivial cycles and the orbit minimum -/

/-- A nontrivial cycle through `n` of period `p` (not necessarily the minimal period). -/
def IsNontrivialCycle (n p : ℕ) : Prop :=
  1 ≤ n ∧ 1 ≤ p ∧ C^[p] n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4

lemma orbit_nonempty (n : ℕ) : ∃ v, ∃ j, C^[j] n = v := ⟨n, 0, rfl⟩

/-- Least value on the forward `C`-orbit of `n`. -/
noncomputable def orbitMin (n : ℕ) : ℕ := by
  classical exact Nat.find (orbit_nonempty n)

lemma orbitMin_mem (n : ℕ) : ∃ a, C^[a] n = orbitMin n := by
  classical exact Nat.find_spec (orbit_nonempty n)

lemma orbitMin_le (n j : ℕ) : orbitMin n ≤ C^[j] n := by
  classical exact Nat.find_min' (orbit_nonempty n) ⟨j, rfl⟩

/-- **Minimal element of a nontrivial cycle.** It lies on the cycle, is `≥ 2`, never
drops below itself, and so has no stopping time. -/
theorem cycleMin_spec {n p : ℕ} (h : IsNontrivialCycle n p) :
    (∃ a, C^[a] n = orbitMin n) ∧ (∃ k, C^[k] (orbitMin n) = n) ∧
    C^[p] (orbitMin n) = orbitMin n ∧ 2 ≤ orbitMin n ∧
    (∀ j, orbitMin n ≤ C^[j] (orbitMin n)) ∧ ¬ HasStoppingTime (orbitMin n) := by
  obtain ⟨hn, hp, hc, h1, h2, h4⟩ := h
  obtain ⟨a, ha⟩ := orbitMin_mem n
  have hret : C^[p * a - a] (orbitMin n) = n := by
    rw [← ha, ← Function.iterate_add_apply,
      show p * a - a + a = p * a by
        have : a ≤ p * a := Nat.le_mul_of_pos_left a hp
        omega,
      C_iterate_mul_period hc]
  have hall : ∀ j, orbitMin n ≤ C^[j] (orbitMin n) := by
    intro j
    have := orbitMin_le n (j + a)
    rwa [Function.iterate_add_apply, ha] at this
  have hpos : 1 ≤ orbitMin n := by rw [← ha]; exact C_iterate_pos hn a
  have hne : orbitMin n ≠ 1 := by
    intro hm
    rw [hm] at hret
    rcases C_iterate_one (p * a - a) with e | e | e <;> rw [e] at hret <;> omega
  refine ⟨⟨a, ha⟩, ⟨_, hret⟩, ?_, by omega, hall, ?_⟩
  · rw [← ha, ← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hc]
  · rintro ⟨j, _, hj⟩
    exact absurd (hall j) (by omega)

/-! ### Kernel verification of small values -/

/-- Fuel-bounded checker: does the `Tt`-trajectory starting at `x` reach a value `< n`
within `f` values (`x, Tt x, …`)? -/
def stopsBelow (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, x => decide (x < n) || stopsBelow n f (Tt x)

/-- Fuel used for the small-value check. -/
def dropFuel : ℕ := 200

lemma stopsBelow_sound (n : ℕ) (f : ℕ) : ∀ x j, stopsBelow n f x = true → x = Tt^[j] n →
    ∃ i, j ≤ i ∧ i < j + f ∧ Tt^[i] n < n := by
  induction f with
  | zero => intro x j h; simp [stopsBelow] at h
  | succ f ih =>
    intro x j h hx
    simp only [stopsBelow, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨j, le_rfl, by omega, hx ▸ h⟩
    · obtain ⟨i, h1, h2, h3⟩ := ih (Tt x) (j + 1) h (by rw [hx, Function.iterate_succ_apply'])
      exact ⟨i, by omega, by omega, h3⟩

/-- Checks `stopsBelow m dropFuel (Tt m)` for all `m ∈ [lo, lo + k)`. -/
def checkAll (lo : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => checkAll lo k && stopsBelow (lo + k) dropFuel (Tt (lo + k))

lemma checkAll_sound (lo : ℕ) (k : ℕ) : checkAll lo k = true →
    ∀ n, lo ≤ n → n < lo + k → stopsBelow n dropFuel (Tt n) = true := by
  induction k with
  | zero => intro _ n _ h; omega
  | succ k ih =>
    intro h n h1 h2
    simp only [checkAll, Bool.and_eq_true] at h
    by_cases hn : n < lo + k
    · exact ih h.1 n h1 hn
    · rw [show n = lo + k by omega]; exact h.2

/-- All `2 ≤ n < N` pass the checker. -/
def smallDrop (N : ℕ) : Prop := ∀ n, 2 ≤ n → n < N → stopsBelow n dropFuel (Tt n) = true

lemma smallDrop_two : smallDrop 2 := fun _ h1 h2 => absurd h2 (by omega)

lemma smallDrop_extend {lo k : ℕ} (h : smallDrop lo) (hc : checkAll lo k = true) :
    smallDrop (lo + k) := by
  intro n h1 h2
  by_cases hn : n < lo
  · exact h n h1 hn
  · exact checkAll_sound lo k hc n (by omega) h2

set_option maxRecDepth 100000

theorem chunkDrop_0 : checkAll 2 16382 = true := by decide +kernel
theorem chunkDrop_1 : checkAll 16384 16384 = true := by decide +kernel
theorem chunkDrop_2 : checkAll 32768 16384 = true := by decide +kernel
theorem chunkDrop_3 : checkAll 49152 16384 = true := by decide +kernel
theorem chunkDrop_4 : checkAll 65536 16384 = true := by decide +kernel
theorem chunkDrop_5 : checkAll 81920 16384 = true := by decide +kernel
theorem chunkDrop_6 : checkAll 98304 16384 = true := by decide +kernel
theorem chunkDrop_7 : checkAll 114688 16384 = true := by decide +kernel
theorem chunkDrop_8 : checkAll 131072 16384 = true := by decide +kernel
theorem chunkDrop_9 : checkAll 147456 16384 = true := by decide +kernel
theorem chunkDrop_10 : checkAll 163840 16384 = true := by decide +kernel
theorem chunkDrop_11 : checkAll 180224 16384 = true := by decide +kernel
theorem chunkDrop_12 : checkAll 196608 16384 = true := by decide +kernel
theorem chunkDrop_13 : checkAll 212992 16384 = true := by decide +kernel
theorem chunkDrop_14 : checkAll 229376 16384 = true := by decide +kernel
theorem chunkDrop_15 : checkAll 245760 16384 = true := by decide +kernel
theorem chunkDrop_16 : checkAll 262144 16384 = true := by decide +kernel
theorem chunkDrop_17 : checkAll 278528 16384 = true := by decide +kernel
theorem chunkDrop_18 : checkAll 294912 16384 = true := by decide +kernel
theorem chunkDrop_19 : checkAll 311296 16384 = true := by decide +kernel
theorem chunkDrop_20 : checkAll 327680 16384 = true := by decide +kernel
theorem chunkDrop_21 : checkAll 344064 16384 = true := by decide +kernel
theorem chunkDrop_22 : checkAll 360448 16384 = true := by decide +kernel
theorem chunkDrop_23 : checkAll 376832 16384 = true := by decide +kernel
theorem chunkDrop_24 : checkAll 393216 16384 = true := by decide +kernel
theorem chunkDrop_25 : checkAll 409600 16384 = true := by decide +kernel
theorem chunkDrop_26 : checkAll 425984 16384 = true := by decide +kernel
theorem chunkDrop_27 : checkAll 442368 16384 = true := by decide +kernel
theorem chunkDrop_28 : checkAll 458752 16384 = true := by decide +kernel
theorem chunkDrop_29 : checkAll 475136 16384 = true := by decide +kernel
theorem chunkDrop_30 : checkAll 491520 16384 = true := by decide +kernel
theorem chunkDrop_31 : checkAll 507904 16384 = true := by decide +kernel
theorem chunkDrop_32 : checkAll 524288 16384 = true := by decide +kernel
theorem chunkDrop_33 : checkAll 540672 16384 = true := by decide +kernel
theorem chunkDrop_34 : checkAll 557056 16384 = true := by decide +kernel
theorem chunkDrop_35 : checkAll 573440 16384 = true := by decide +kernel
theorem chunkDrop_36 : checkAll 589824 16384 = true := by decide +kernel
theorem chunkDrop_37 : checkAll 606208 16384 = true := by decide +kernel
theorem chunkDrop_38 : checkAll 622592 16384 = true := by decide +kernel
theorem chunkDrop_39 : checkAll 638976 16384 = true := by decide +kernel
theorem chunkDrop_40 : checkAll 655360 16384 = true := by decide +kernel
theorem chunkDrop_41 : checkAll 671744 16384 = true := by decide +kernel
theorem chunkDrop_42 : checkAll 688128 16384 = true := by decide +kernel
theorem chunkDrop_43 : checkAll 704512 16384 = true := by decide +kernel
theorem chunkDrop_44 : checkAll 720896 16384 = true := by decide +kernel
theorem chunkDrop_45 : checkAll 737280 16384 = true := by decide +kernel
theorem chunkDrop_46 : checkAll 753664 16384 = true := by decide +kernel
theorem chunkDrop_47 : checkAll 770048 16384 = true := by decide +kernel
theorem chunkDrop_48 : checkAll 786432 16384 = true := by decide +kernel
theorem chunkDrop_49 : checkAll 802816 16384 = true := by decide +kernel
theorem chunkDrop_50 : checkAll 819200 16384 = true := by decide +kernel
theorem chunkDrop_51 : checkAll 835584 16384 = true := by decide +kernel
theorem chunkDrop_52 : checkAll 851968 16384 = true := by decide +kernel
theorem chunkDrop_53 : checkAll 868352 16384 = true := by decide +kernel
theorem chunkDrop_54 : checkAll 884736 16384 = true := by decide +kernel
theorem chunkDrop_55 : checkAll 901120 16384 = true := by decide +kernel
theorem chunkDrop_56 : checkAll 917504 16384 = true := by decide +kernel
theorem chunkDrop_57 : checkAll 933888 16384 = true := by decide +kernel
theorem chunkDrop_58 : checkAll 950272 16384 = true := by decide +kernel
theorem chunkDrop_59 : checkAll 966656 16384 = true := by decide +kernel
theorem chunkDrop_60 : checkAll 983040 16384 = true := by decide +kernel
theorem chunkDrop_61 : checkAll 999424 16384 = true := by decide +kernel
theorem chunkDrop_62 : checkAll 1015808 16384 = true := by decide +kernel
theorem chunkDrop_63 : checkAll 1032192 16384 = true := by decide +kernel

theorem smallDrop_2pow20 : smallDrop 1048576 := by
  have h0 : smallDrop 16384 := smallDrop_extend smallDrop_two chunkDrop_0
  have h1 : smallDrop 32768 := smallDrop_extend h0 chunkDrop_1
  have h2 : smallDrop 49152 := smallDrop_extend h1 chunkDrop_2
  have h3 : smallDrop 65536 := smallDrop_extend h2 chunkDrop_3
  have h4 : smallDrop 81920 := smallDrop_extend h3 chunkDrop_4
  have h5 : smallDrop 98304 := smallDrop_extend h4 chunkDrop_5
  have h6 : smallDrop 114688 := smallDrop_extend h5 chunkDrop_6
  have h7 : smallDrop 131072 := smallDrop_extend h6 chunkDrop_7
  have h8 : smallDrop 147456 := smallDrop_extend h7 chunkDrop_8
  have h9 : smallDrop 163840 := smallDrop_extend h8 chunkDrop_9
  have h10 : smallDrop 180224 := smallDrop_extend h9 chunkDrop_10
  have h11 : smallDrop 196608 := smallDrop_extend h10 chunkDrop_11
  have h12 : smallDrop 212992 := smallDrop_extend h11 chunkDrop_12
  have h13 : smallDrop 229376 := smallDrop_extend h12 chunkDrop_13
  have h14 : smallDrop 245760 := smallDrop_extend h13 chunkDrop_14
  have h15 : smallDrop 262144 := smallDrop_extend h14 chunkDrop_15
  have h16 : smallDrop 278528 := smallDrop_extend h15 chunkDrop_16
  have h17 : smallDrop 294912 := smallDrop_extend h16 chunkDrop_17
  have h18 : smallDrop 311296 := smallDrop_extend h17 chunkDrop_18
  have h19 : smallDrop 327680 := smallDrop_extend h18 chunkDrop_19
  have h20 : smallDrop 344064 := smallDrop_extend h19 chunkDrop_20
  have h21 : smallDrop 360448 := smallDrop_extend h20 chunkDrop_21
  have h22 : smallDrop 376832 := smallDrop_extend h21 chunkDrop_22
  have h23 : smallDrop 393216 := smallDrop_extend h22 chunkDrop_23
  have h24 : smallDrop 409600 := smallDrop_extend h23 chunkDrop_24
  have h25 : smallDrop 425984 := smallDrop_extend h24 chunkDrop_25
  have h26 : smallDrop 442368 := smallDrop_extend h25 chunkDrop_26
  have h27 : smallDrop 458752 := smallDrop_extend h26 chunkDrop_27
  have h28 : smallDrop 475136 := smallDrop_extend h27 chunkDrop_28
  have h29 : smallDrop 491520 := smallDrop_extend h28 chunkDrop_29
  have h30 : smallDrop 507904 := smallDrop_extend h29 chunkDrop_30
  have h31 : smallDrop 524288 := smallDrop_extend h30 chunkDrop_31
  have h32 : smallDrop 540672 := smallDrop_extend h31 chunkDrop_32
  have h33 : smallDrop 557056 := smallDrop_extend h32 chunkDrop_33
  have h34 : smallDrop 573440 := smallDrop_extend h33 chunkDrop_34
  have h35 : smallDrop 589824 := smallDrop_extend h34 chunkDrop_35
  have h36 : smallDrop 606208 := smallDrop_extend h35 chunkDrop_36
  have h37 : smallDrop 622592 := smallDrop_extend h36 chunkDrop_37
  have h38 : smallDrop 638976 := smallDrop_extend h37 chunkDrop_38
  have h39 : smallDrop 655360 := smallDrop_extend h38 chunkDrop_39
  have h40 : smallDrop 671744 := smallDrop_extend h39 chunkDrop_40
  have h41 : smallDrop 688128 := smallDrop_extend h40 chunkDrop_41
  have h42 : smallDrop 704512 := smallDrop_extend h41 chunkDrop_42
  have h43 : smallDrop 720896 := smallDrop_extend h42 chunkDrop_43
  have h44 : smallDrop 737280 := smallDrop_extend h43 chunkDrop_44
  have h45 : smallDrop 753664 := smallDrop_extend h44 chunkDrop_45
  have h46 : smallDrop 770048 := smallDrop_extend h45 chunkDrop_46
  have h47 : smallDrop 786432 := smallDrop_extend h46 chunkDrop_47
  have h48 : smallDrop 802816 := smallDrop_extend h47 chunkDrop_48
  have h49 : smallDrop 819200 := smallDrop_extend h48 chunkDrop_49
  have h50 : smallDrop 835584 := smallDrop_extend h49 chunkDrop_50
  have h51 : smallDrop 851968 := smallDrop_extend h50 chunkDrop_51
  have h52 : smallDrop 868352 := smallDrop_extend h51 chunkDrop_52
  have h53 : smallDrop 884736 := smallDrop_extend h52 chunkDrop_53
  have h54 : smallDrop 901120 := smallDrop_extend h53 chunkDrop_54
  have h55 : smallDrop 917504 := smallDrop_extend h54 chunkDrop_55
  have h56 : smallDrop 933888 := smallDrop_extend h55 chunkDrop_56
  have h57 : smallDrop 950272 := smallDrop_extend h56 chunkDrop_57
  have h58 : smallDrop 966656 := smallDrop_extend h57 chunkDrop_58
  have h59 : smallDrop 983040 := smallDrop_extend h58 chunkDrop_59
  have h60 : smallDrop 999424 := smallDrop_extend h59 chunkDrop_60
  have h61 : smallDrop 1015808 := smallDrop_extend h60 chunkDrop_61
  have h62 : smallDrop 1032192 := smallDrop_extend h61 chunkDrop_62
  have h63 : smallDrop 1048576 := smallDrop_extend h62 chunkDrop_63
  exact h63

/-- **Small values drop (kernel-verified).** Every `2 ≤ n ≤ 2^20` has some `1 ≤ i ≤ 400`
with `C^[i] n < n`. -/
theorem small_drop {n : ℕ} (h1 : 2 ≤ n) (h2 : n ≤ 2 ^ 20) :
    ∃ i, 1 ≤ i ∧ i ≤ 400 ∧ C^[i] n < n := by
  by_cases hN : n < 2 ^ 20
  · have hs := smallDrop_2pow20 n h1 (by simpa using hN)
    obtain ⟨j, hj1, hj2, hj3⟩ := stopsBelow_sound n dropFuel (Tt n) 1 hs (by simp)
    refine ⟨j + oddCount j n, by omega, ?_, by rwa [← Tt_iterate_eq_C_iterate]⟩
    have := oddCount_le j n
    simp only [dropFuel] at hj2
    omega
  · refine ⟨1, le_rfl, by norm_num, ?_⟩
    rw [show n = 2 ^ 20 by omega]; decide

/-- Every `2 ≤ n ≤ 2^20` has finite stopping time. -/
theorem stoppingTime_le_2pow20 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 2 ^ 20) :
    n = 1 ∨ HasStoppingTime n := by
  by_cases h : n = 1
  · exact Or.inl h
  · obtain ⟨i, hi1, _, hi3⟩ := small_drop (n := n) (by omega) h2
    exact Or.inr ⟨i, hi1, hi3⟩

/-- **Collatz conjecture verified for `1 ≤ n ≤ 2^20`** (kernel computation). -/
theorem reaches_one_le_2pow20 : ∀ n, 1 ≤ n → n ≤ 2 ^ 20 → ∃ k, C^[k] n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h1 h2
    by_cases hn : n = 1
    · exact ⟨0, by simp [hn]⟩
    · obtain ⟨i, _, _, hi3⟩ := small_drop (n := n) (by omega) h2
      have hpos := C_iterate_pos h1 i
      obtain ⟨k, hk⟩ := ih _ hi3 hpos (by omega)
      exact ⟨k + i, by rw [Function.iterate_add_apply, hk]⟩

/-! ### Combination theorem -/

/-- **Constraints on nontrivial cycles.** If `n` lies on a nontrivial cycle, the minimal
element `m = orbitMin n` of the cycle satisfies `2^20 < m`, and its residue mod `2^18` is one of
the `7495` classes in `uncertified 18`. -/
theorem nontrivial_cycle_constraints {n p : ℕ} (h : IsNontrivialCycle n p) :
    2 ^ 20 < orbitMin n ∧ orbitMin n % 2 ^ 18 ∈ uncertified 18 ∧
    (uncertified 18).card = 7495 := by
  obtain ⟨_, _, _, hm2, hall, _⟩ := cycleMin_spec h
  have hB : 2 ^ 20 < orbitMin n := by
    by_contra hc
    obtain ⟨i, _, _, hi⟩ := small_drop hm2 (by omega)
    exact absurd (hall i) (by omega)
  refine ⟨hB, ?_, density_certificate_18.1⟩
  by_contra hU
  have hcert : certB 18 (orbitMin n % 2 ^ 18) = true := by
    by_contra hc
    exact hU (Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ (by positivity)),
      by simpa using hc⟩)
  obtain ⟨i, _, _, hi⟩ := certB_sound_C (le_of_lt (lt_of_le_of_lt (by norm_num) hB)) hcert
  exact absurd (hall i) (by omega)

/-- Every element of a nontrivial cycle is `> 2^20`. -/
theorem nontrivial_cycle_elements_gt {n p : ℕ} (h : IsNontrivialCycle n p) (j : ℕ) :
    2 ^ 20 < C^[j] n :=
  lt_of_lt_of_le (nontrivial_cycle_constraints h).1 (orbitMin_le n j)

/-- **No small nontrivial cycle.** If `1 ≤ n ≤ 2^20` and `C^[p] n = n` with `p ≥ 1`, then
`n ∈ {1, 2, 4}`. -/
theorem no_small_nontrivial_cycle {n p : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 2 ^ 20) (hp : 1 ≤ p)
    (hc : C^[p] n = n) : n = 1 ∨ n = 2 ∨ n = 4 := by
  by_contra hne
  have hcyc : IsNontrivialCycle n p := ⟨h1, hp, hc, by omega, by omega, by omega⟩
  have := nontrivial_cycle_elements_gt hcyc 0
  simp at this; omega

end APEX.Collatz

