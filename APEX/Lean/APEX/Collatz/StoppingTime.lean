import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import APEX.Collatz.BoundedCorrection

/-!
# Collatz: stopping-time certificates (Terras' parity-vector method)

Maps:
* `C n = n/2` (n even), `3n+1` (n odd): the standard Collatz map.
* `Tt n = n/2` (n even), `(3n+1)/2` (n odd): the Terras map; every orbit of `Tt` is a
  subsequence of the `C` orbit (`Tt_iterate_eq_C_iterate`).
* `oddCount j a` = number of odd values among `Tt^[0] a, …, Tt^[j-1] a`.

Proved (all kernel-checked, no `native_decide`):
1. **Terras affine lemma** (`Tt_iterate_affine`, `Tt_iterate_parity`, `oddCount_add_two_pow`):
   for `n = a + 2^k t`, the first `k` steps of `Tt` have the same parities as for `a`, and
   `Tt^[k] (a + 2^k t) = 3^(oddCount k a) * t + Tt^[k] a` for every `t`.
2. **Certificate theorem** (`certAt_sound`, `certB_sound`): if for a residue `a` (mod `2^k`)
   some `1 ≤ j ≤ k` has `3^(e_j) < 2^j` and the affine map at step `j` is below the identity at
   `t = 1`, then every `n ≥ 2^k` with `n ≡ a (mod 2^k)` has `Tt^[j] n < n`, hence `C^[i] n < n`
   for some `1 ≤ i ≤ 2k`.  `certB` is a decidable checker over residues.
3. **Kernel computation** (`countBad_eq_*`): the number of residue classes mod `2^k` NOT certified
   is `1,1,2,3,4,8,13,19,38,64,128,226` for `k = 1..12` (matches OEIS A076227) and `7495` for
   `k = 18` (chunked kernel computation, `countFrom_18`).  Consequence (`density_certificate`): every `n ≥ 2^K` outside the `N_K` uncertified
   residue classes mod `2^K` has finite stopping time (≤ `K` for `Tt`, ≤ `2K` for `C`); i.e. the
   possibly-non-stopping `n` lie in a set of residues of density `N_K / 2^K`.

**Caveat.** This is a classical *partial* result (Terras 1976, Everett 1977: almost all `n` have
finite stopping time; here only the finite-`K` density bounds are certified).  It does NOT prove
the Collatz conjecture: uncertified classes remain for every `K` (the density only tends to 0),
and the numbers `n < 2^K` are not treated here.  (Finite stopping time for *every* `n ≥ 2` would
imply the conjecture by strong induction; that is exactly what is missing.)
-/

namespace APEX.Collatz

/-- Standard Collatz map. -/
def C (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Terras (shortcut) Collatz map. -/
def Tt (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Relation with the registered Syracuse map `T` of `BoundedCorrection`. -/
lemma T_eq_oddPart_C {n : ℕ} (hn : n % 2 = 1) : T n = oddPart (C n) := by
  unfold T C; rw [if_neg (by omega)]

/-- Number of odd values among the first `i` iterates `Tt^[0] a, …, Tt^[i-1] a`. -/
def oddCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | i + 1, a => a % 2 + oddCount i (Tt a)

lemma oddCount_succ' (i : ℕ) : ∀ a, oddCount (i + 1) a = oddCount i a + Tt^[i] a % 2 := by
  induction i with
  | zero => intro a; simp [oddCount]
  | succ i ih =>
    intro a
    rw [oddCount, ih (Tt a), oddCount, Function.iterate_succ_apply]; ring

lemma oddCount_le (i : ℕ) : ∀ a, oddCount i a ≤ i := by
  induction i with
  | zero => intro a; simp [oddCount]
  | succ i ih => intro a; rw [oddCount]; have := ih (Tt a); omega

lemma Tt_add (a i s : ℕ) : Tt (a + 2 ^ (i + 1) * s) = Tt a + 3 ^ (a % 2) * (2 ^ i * s) := by
  have e : 2 ^ (i + 1) * s = 2 * (2 ^ i * s) := by rw [pow_succ]; ring
  rw [e]
  generalize 2 ^ i * s = X
  unfold Tt
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · rw [if_pos (by omega), if_pos h, h]; simp; omega
  · rw [if_neg (by omega), if_neg (by omega), h]; simp; omega

/-- **Terras affine lemma** (general form). -/
theorem Tt_iterate_affine (i : ℕ) :
    ∀ a s, Tt^[i] (a + 2 ^ i * s) = Tt^[i] a + 3 ^ (oddCount i a) * s := by
  induction i with
  | zero => intro a s; simp [oddCount]
  | succ i ih =>
    intro a s
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Tt_add,
      show 3 ^ (a % 2) * (2 ^ i * s) = 2 ^ i * (3 ^ (a % 2) * s) by ring, ih, oddCount, pow_add]
    ring

/-- Parity pattern: the first `k` steps on `a + 2^k t` have the same parities as on `a`. -/
theorem Tt_iterate_parity (k a t i : ℕ) (hi : i < k) :
    Tt^[i] (a + 2 ^ k * t) % 2 = Tt^[i] a % 2 := by
  have e : 2 ^ k * t = 2 ^ i * (2 * (2 ^ (k - i - 1) * t)) := by
    rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_add, show i + 1 + (k - i - 1) = k by omega]
  rw [e, Tt_iterate_affine]
  rw [show 3 ^ oddCount i a * (2 * (2 ^ (k - i - 1) * t)) =
    2 * (3 ^ oddCount i a * (2 ^ (k - i - 1) * t)) by ring]
  omega

/-- The number of odd steps among the first `i ≤ k` steps only depends on the residue mod `2^k`. -/
theorem oddCount_add_two_pow (k a t : ℕ) : ∀ i, i ≤ k → oddCount i (a + 2 ^ k * t) = oddCount i a := by
  intro i
  induction i with
  | zero => intro; simp [oddCount]
  | succ i ih =>
    intro hi
    rw [oddCount_succ', oddCount_succ', ih (by omega), Tt_iterate_parity k a t i (by omega)]

/-- **Goal 1 (Terras):** fixed parity pattern and `Tt^[k] (a + 2^k t) = 3^e t + Tt^[k] a`. -/
theorem terras_affine (k a t : ℕ) :
    (∀ i < k, Tt^[i] (a + 2 ^ k * t) % 2 = Tt^[i] a % 2) ∧
    oddCount k (a + 2 ^ k * t) = oddCount k a ∧
    Tt^[k] (a + 2 ^ k * t) = 3 ^ (oddCount k a) * t + Tt^[k] a := by
  refine ⟨fun i hi => Tt_iterate_parity k a t i hi, oddCount_add_two_pow k a t k le_rfl, ?_⟩
  rw [Tt_iterate_affine, add_comm]

/-! ### Relation with the standard map `C` -/

lemma Tt_eq_C_iterate (n : ℕ) : Tt n = C^[1 + n % 2] n := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h]; simp [Tt, C, h]
  · rw [h]
    show Tt n = C (C n)
    have h1 : C n = 3 * n + 1 := by unfold C; rw [if_neg (by omega)]
    rw [h1]; unfold C Tt
    rw [if_neg (show ¬ n % 2 = 0 by omega), if_pos (show (3 * n + 1) % 2 = 0 by omega)]

theorem Tt_iterate_eq_C_iterate (i : ℕ) : ∀ n, Tt^[i] n = C^[i + oddCount i n] n := by
  induction i with
  | zero => intro n; simp [oddCount]
  | succ i ih =>
    intro n
    rw [Function.iterate_succ_apply, ih (Tt n), oddCount]
    have hT := Tt_eq_C_iterate n
    generalize oddCount i (Tt n) = m
    rw [hT, ← Function.iterate_add_apply]
    congr 1; omega

/-! ### Certificates -/

/-- Certificate at step `j` for residue `a` mod `2^k`: slope `3^e < 2^j` and the affine map
`t ↦ Tt^[j] a + 3^e 2^(k-j) t` is below `t ↦ a + 2^k t` at `t = 1`. -/
def certAt (k a j : ℕ) : Bool :=
  decide (1 ≤ j) && decide (j ≤ k) && decide (3 ^ (oddCount j a) < 2 ^ j) &&
    decide (Tt^[j] a + 3 ^ (oddCount j a) * 2 ^ (k - j) < a + 2 ^ k)

/-- **Certificate theorem.** -/
theorem certAt_sound {k a j : ℕ} (h : certAt k a j = true) (t : ℕ) (ht : 1 ≤ t) :
    Tt^[j] (a + 2 ^ k * t) < a + 2 ^ k * t := by
  simp only [certAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hjk⟩, hslope⟩, hconst⟩ := h
  have e : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← pow_add]; congr 1; omega
  rw [e] at hconst
  rw [e, mul_assoc, Tt_iterate_affine]
  generalize 3 ^ oddCount j a = E at *
  generalize 2 ^ j = Q at *
  generalize 2 ^ (k - j) = P at *
  generalize Tt^[j] a = X at *
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  have h1 : E * (P * u) ≤ Q * (P * u) := Nat.mul_le_mul_right _ hslope.le
  nlinarith

/-- Efficient checker: walks the `Tt`-trajectory once, tracking `x = Tt^[j] a`, `e = oddCount j a`. -/
def scan (k a : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | f + 1, j, x, e =>
    (decide (3 ^ (e + x % 2) < 2 ^ (j + 1)) &&
      decide (Tt x + 3 ^ (e + x % 2) * 2 ^ (k - (j + 1)) < a + 2 ^ k)) ||
    scan k a f (j + 1) (Tt x) (e + x % 2)

/-- Decidable certificate for residue `a` mod `2^k`. -/
def certB (k a : ℕ) : Bool := scan k a k 0 a 0

lemma scan_sound (k a : ℕ) (f : ℕ) : ∀ j x e, scan k a f j x e = true → x = Tt^[j] a →
    e = oddCount j a → j + f ≤ k → ∃ j', j < j' ∧ j' ≤ j + f ∧ certAt k a j' = true := by
  induction f with
  | zero => intro j x e h; simp [scan] at h
  | succ f ih =>
    intro j x e h hx he hjf
    simp only [scan, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · refine ⟨j + 1, by omega, by omega, ?_⟩
      have hx' : Tt x = Tt^[j + 1] a := by rw [hx, Function.iterate_succ_apply']
      have he' : e + x % 2 = oddCount (j + 1) a := by rw [oddCount_succ', he, hx]
      simp only [certAt, Bool.and_eq_true, decide_eq_true_eq]
      rw [← hx', ← he']
      exact ⟨⟨⟨by omega, by omega⟩, h1⟩, h2⟩
    · obtain ⟨j', h1, h2, h3⟩ := ih (j + 1) _ _ h
        (by rw [hx, Function.iterate_succ_apply'])
        (by rw [oddCount_succ', he, hx]) (by omega)
      exact ⟨j', by omega, by omega, h3⟩

lemma certB_sound' {k a : ℕ} (h : certB k a = true) : ∃ j, 1 ≤ j ∧ j ≤ k ∧ certAt k a j = true := by
  obtain ⟨j, h1, h2, h3⟩ := scan_sound k a k 0 a 0 h (by simp) (by simp [oddCount]) (by omega)
  exact ⟨j, h1, by omega, h3⟩

/-- **Certificate theorem (checker form).** If the residue of `n` mod `2^k` is certified and
`n ≥ 2^k`, then `n` has `Tt`-stopping time `≤ k`. -/
theorem certB_sound {k n : ℕ} (hn : 2 ^ k ≤ n) (h : certB k (n % 2 ^ k) = true) :
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ Tt^[j] n < n := by
  obtain ⟨j, h1, h2, h3⟩ := certB_sound' h
  have hd : n = n % 2 ^ k + 2 ^ k * (n / 2 ^ k) := (Nat.mod_add_div n (2 ^ k)).symm
  have ht : 1 ≤ n / 2 ^ k := (Nat.one_le_div_iff (by positivity)).2 hn
  refine ⟨j, h1, h2, ?_⟩
  rw [hd]; exact certAt_sound h3 _ ht

/-- `C`-version: the standard Collatz map drops below `n` within `2k` steps. -/
theorem certB_sound_C {k n : ℕ} (hn : 2 ^ k ≤ n) (h : certB k (n % 2 ^ k) = true) :
    ∃ i, 1 ≤ i ∧ i ≤ 2 * k ∧ C^[i] n < n := by
  obtain ⟨j, h1, h2, h3⟩ := certB_sound hn h
  refine ⟨j + oddCount j n, by omega, ?_, by rwa [← Tt_iterate_eq_C_iterate]⟩
  have := oddCount_le j n; omega

/-! ### Stopping time -/

/-- `n` has finite stopping time for the standard map `C`. -/
def HasStoppingTime (n : ℕ) : Prop := ∃ j, 1 ≤ j ∧ C^[j] n < n

/-- Stopping time `σ(n)` = least `j ≥ 1` with `C^[j] n < n`. -/
noncomputable def stoppingTime (n : ℕ) (h : HasStoppingTime n) : ℕ := by
  classical exact Nat.find h

theorem stoppingTime_spec (n : ℕ) (h : HasStoppingTime n) :
    1 ≤ stoppingTime n h ∧ C^[stoppingTime n h] n < n := by
  classical exact Nat.find_spec h

theorem stoppingTime_le_of_certB {k n : ℕ} (hn : 2 ^ k ≤ n) (h : certB k (n % 2 ^ k) = true) :
    ∃ hs : HasStoppingTime n, stoppingTime n hs ≤ 2 * k := by
  obtain ⟨i, h1, h2, h3⟩ := certB_sound_C hn h
  have hs : HasStoppingTime n := ⟨i, h1, h3⟩
  refine ⟨hs, ?_⟩
  classical
  exact le_trans (Nat.find_min' hs ⟨h1, h3⟩) h2

/-! ### Counting uncertified classes (kernel computation) -/

/-- Number of `a < m` that are not certified at level `k`. -/
def countFrom (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => countFrom k m + (if certB k m then 0 else 1)

/-- The set of residues mod `2^k` not certified by `certB`. -/
def uncertified (k : ℕ) : Finset ℕ := (Finset.range (2 ^ k)).filter (fun a => certB k a = false)

lemma countFrom_eq (k m : ℕ) :
    countFrom k m = ((Finset.range m).filter (fun a => certB k a = false)).card := by
  induction m with
  | zero => simp [countFrom]
  | succ m ih =>
    rw [countFrom, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : certB k m = true
    · simp [h]
    · have h' : certB k m = false := by simpa using h
      rw [if_pos h', Finset.card_insert_of_notMem (by simp), if_neg h]

theorem uncertified_card (k : ℕ) : (uncertified k).card = countFrom k (2 ^ k) :=
  (countFrom_eq k _).symm

theorem countBad_eq_1_12 :
    [countFrom 1 2, countFrom 2 4, countFrom 3 8, countFrom 4 16, countFrom 5 32, countFrom 6 64,
     countFrom 7 128, countFrom 8 256, countFrom 9 512, countFrom 10 1024, countFrom 11 2048,
     countFrom 12 4096] = [1, 1, 2, 3, 4, 8, 13, 19, 38, 64, 128, 226] := by
  decide +kernel

/-- **Density certificate** at level `12`: every `n ≥ 2^12` outside 226 residue classes
mod `2^12` (density `226/4096 < 5.52%`) has stopping time `≤ 24` for `C` (`≤ 12` for `Tt`). -/
theorem density_certificate_12 :
    (uncertified 12).card = 226 ∧
    ∀ n, 2 ^ 12 ≤ n → n % 2 ^ 12 ∉ uncertified 12 →
      ∃ hs : HasStoppingTime n, stoppingTime n hs ≤ 24 := by
  refine ⟨?_, fun n hn hU => ?_⟩
  · rw [uncertified_card]
    have := congrArg (fun l => l[11]!) countBad_eq_1_12
    simpa using this
  · have h : certB 12 (n % 2 ^ 12) = true := by
      by_contra hc
      exact hU (Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ (by positivity)),
        by simpa using hc⟩)
    exact stoppingTime_le_of_certB hn h


/-! ### Level 18 (chunked kernel computation, 64 chunks of 4096 residues) -/

/-- Number of `a ∈ [lo, lo+n)` not certified at level `k`. -/
def countRange (k lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => countRange k lo n + (if certB k (lo + n) then 0 else 1)

lemma countFrom_add (k m : ℕ) : ∀ n, countFrom k (m + n) = countFrom k m + countRange k m n := by
  intro n
  induction n with
  | zero => simp [countRange]
  | succ n ih =>
    show countFrom k ((m + n) + 1) = _
    rw [countFrom, ih, countRange]; ring

theorem chunk18_0 : countRange 18 0 4096 = 116 := by decide +kernel
theorem chunk18_1 : countRange 18 4096 4096 = 114 := by decide +kernel
theorem chunk18_2 : countRange 18 8192 4096 = 123 := by decide +kernel
theorem chunk18_3 : countRange 18 12288 4096 = 111 := by decide +kernel
theorem chunk18_4 : countRange 18 16384 4096 = 121 := by decide +kernel
theorem chunk18_5 : countRange 18 20480 4096 = 114 := by decide +kernel
theorem chunk18_6 : countRange 18 24576 4096 = 112 := by decide +kernel
theorem chunk18_7 : countRange 18 28672 4096 = 122 := by decide +kernel
theorem chunk18_8 : countRange 18 32768 4096 = 118 := by decide +kernel
theorem chunk18_9 : countRange 18 36864 4096 = 122 := by decide +kernel
theorem chunk18_10 : countRange 18 40960 4096 = 117 := by decide +kernel
theorem chunk18_11 : countRange 18 45056 4096 = 116 := by decide +kernel
theorem chunk18_12 : countRange 18 49152 4096 = 118 := by decide +kernel
theorem chunk18_13 : countRange 18 53248 4096 = 111 := by decide +kernel
theorem chunk18_14 : countRange 18 57344 4096 = 116 := by decide +kernel
theorem chunk18_15 : countRange 18 61440 4096 = 113 := by decide +kernel
theorem chunk18_16 : countRange 18 65536 4096 = 112 := by decide +kernel
theorem chunk18_17 : countRange 18 69632 4096 = 112 := by decide +kernel
theorem chunk18_18 : countRange 18 73728 4096 = 122 := by decide +kernel
theorem chunk18_19 : countRange 18 77824 4096 = 116 := by decide +kernel
theorem chunk18_20 : countRange 18 81920 4096 = 121 := by decide +kernel
theorem chunk18_21 : countRange 18 86016 4096 = 119 := by decide +kernel
theorem chunk18_22 : countRange 18 90112 4096 = 120 := by decide +kernel
theorem chunk18_23 : countRange 18 94208 4096 = 121 := by decide +kernel
theorem chunk18_24 : countRange 18 98304 4096 = 112 := by decide +kernel
theorem chunk18_25 : countRange 18 102400 4096 = 108 := by decide +kernel
theorem chunk18_26 : countRange 18 106496 4096 = 117 := by decide +kernel
theorem chunk18_27 : countRange 18 110592 4096 = 112 := by decide +kernel
theorem chunk18_28 : countRange 18 114688 4096 = 121 := by decide +kernel
theorem chunk18_29 : countRange 18 118784 4096 = 114 := by decide +kernel
theorem chunk18_30 : countRange 18 122880 4096 = 114 := by decide +kernel
theorem chunk18_31 : countRange 18 126976 4096 = 122 := by decide +kernel
theorem chunk18_32 : countRange 18 131072 4096 = 119 := by decide +kernel
theorem chunk18_33 : countRange 18 135168 4096 = 116 := by decide +kernel
theorem chunk18_34 : countRange 18 139264 4096 = 127 := by decide +kernel
theorem chunk18_35 : countRange 18 143360 4096 = 117 := by decide +kernel
theorem chunk18_36 : countRange 18 147456 4096 = 122 := by decide +kernel
theorem chunk18_37 : countRange 18 151552 4096 = 110 := by decide +kernel
theorem chunk18_38 : countRange 18 155648 4096 = 118 := by decide +kernel
theorem chunk18_39 : countRange 18 159744 4096 = 115 := by decide +kernel
theorem chunk18_40 : countRange 18 163840 4096 = 118 := by decide +kernel
theorem chunk18_41 : countRange 18 167936 4096 = 112 := by decide +kernel
theorem chunk18_42 : countRange 18 172032 4096 = 117 := by decide +kernel
theorem chunk18_43 : countRange 18 176128 4096 = 120 := by decide +kernel
theorem chunk18_44 : countRange 18 180224 4096 = 116 := by decide +kernel
theorem chunk18_45 : countRange 18 184320 4096 = 121 := by decide +kernel
theorem chunk18_46 : countRange 18 188416 4096 = 122 := by decide +kernel
theorem chunk18_47 : countRange 18 192512 4096 = 120 := by decide +kernel
theorem chunk18_48 : countRange 18 196608 4096 = 122 := by decide +kernel
theorem chunk18_49 : countRange 18 200704 4096 = 115 := by decide +kernel
theorem chunk18_50 : countRange 18 204800 4096 = 122 := by decide +kernel
theorem chunk18_51 : countRange 18 208896 4096 = 107 := by decide +kernel
theorem chunk18_52 : countRange 18 212992 4096 = 122 := by decide +kernel
theorem chunk18_53 : countRange 18 217088 4096 = 112 := by decide +kernel
theorem chunk18_54 : countRange 18 221184 4096 = 113 := by decide +kernel
theorem chunk18_55 : countRange 18 225280 4096 = 119 := by decide +kernel
theorem chunk18_56 : countRange 18 229376 4096 = 113 := by decide +kernel
theorem chunk18_57 : countRange 18 233472 4096 = 123 := by decide +kernel
theorem chunk18_58 : countRange 18 237568 4096 = 121 := by decide +kernel
theorem chunk18_59 : countRange 18 241664 4096 = 121 := by decide +kernel
theorem chunk18_60 : countRange 18 245760 4096 = 122 := by decide +kernel
theorem chunk18_61 : countRange 18 249856 4096 = 118 := by decide +kernel
theorem chunk18_62 : countRange 18 253952 4096 = 118 := by decide +kernel
theorem chunk18_63 : countRange 18 258048 4096 = 110 := by decide +kernel
theorem countFrom_18 : countFrom 18 262144 = 7495 := by
  rw [show (262144 : ℕ) = 258048 + 4096 from rfl, countFrom_add, chunk18_63]
  rw [show (258048 : ℕ) = 253952 + 4096 from rfl, countFrom_add, chunk18_62]
  rw [show (253952 : ℕ) = 249856 + 4096 from rfl, countFrom_add, chunk18_61]
  rw [show (249856 : ℕ) = 245760 + 4096 from rfl, countFrom_add, chunk18_60]
  rw [show (245760 : ℕ) = 241664 + 4096 from rfl, countFrom_add, chunk18_59]
  rw [show (241664 : ℕ) = 237568 + 4096 from rfl, countFrom_add, chunk18_58]
  rw [show (237568 : ℕ) = 233472 + 4096 from rfl, countFrom_add, chunk18_57]
  rw [show (233472 : ℕ) = 229376 + 4096 from rfl, countFrom_add, chunk18_56]
  rw [show (229376 : ℕ) = 225280 + 4096 from rfl, countFrom_add, chunk18_55]
  rw [show (225280 : ℕ) = 221184 + 4096 from rfl, countFrom_add, chunk18_54]
  rw [show (221184 : ℕ) = 217088 + 4096 from rfl, countFrom_add, chunk18_53]
  rw [show (217088 : ℕ) = 212992 + 4096 from rfl, countFrom_add, chunk18_52]
  rw [show (212992 : ℕ) = 208896 + 4096 from rfl, countFrom_add, chunk18_51]
  rw [show (208896 : ℕ) = 204800 + 4096 from rfl, countFrom_add, chunk18_50]
  rw [show (204800 : ℕ) = 200704 + 4096 from rfl, countFrom_add, chunk18_49]
  rw [show (200704 : ℕ) = 196608 + 4096 from rfl, countFrom_add, chunk18_48]
  rw [show (196608 : ℕ) = 192512 + 4096 from rfl, countFrom_add, chunk18_47]
  rw [show (192512 : ℕ) = 188416 + 4096 from rfl, countFrom_add, chunk18_46]
  rw [show (188416 : ℕ) = 184320 + 4096 from rfl, countFrom_add, chunk18_45]
  rw [show (184320 : ℕ) = 180224 + 4096 from rfl, countFrom_add, chunk18_44]
  rw [show (180224 : ℕ) = 176128 + 4096 from rfl, countFrom_add, chunk18_43]
  rw [show (176128 : ℕ) = 172032 + 4096 from rfl, countFrom_add, chunk18_42]
  rw [show (172032 : ℕ) = 167936 + 4096 from rfl, countFrom_add, chunk18_41]
  rw [show (167936 : ℕ) = 163840 + 4096 from rfl, countFrom_add, chunk18_40]
  rw [show (163840 : ℕ) = 159744 + 4096 from rfl, countFrom_add, chunk18_39]
  rw [show (159744 : ℕ) = 155648 + 4096 from rfl, countFrom_add, chunk18_38]
  rw [show (155648 : ℕ) = 151552 + 4096 from rfl, countFrom_add, chunk18_37]
  rw [show (151552 : ℕ) = 147456 + 4096 from rfl, countFrom_add, chunk18_36]
  rw [show (147456 : ℕ) = 143360 + 4096 from rfl, countFrom_add, chunk18_35]
  rw [show (143360 : ℕ) = 139264 + 4096 from rfl, countFrom_add, chunk18_34]
  rw [show (139264 : ℕ) = 135168 + 4096 from rfl, countFrom_add, chunk18_33]
  rw [show (135168 : ℕ) = 131072 + 4096 from rfl, countFrom_add, chunk18_32]
  rw [show (131072 : ℕ) = 126976 + 4096 from rfl, countFrom_add, chunk18_31]
  rw [show (126976 : ℕ) = 122880 + 4096 from rfl, countFrom_add, chunk18_30]
  rw [show (122880 : ℕ) = 118784 + 4096 from rfl, countFrom_add, chunk18_29]
  rw [show (118784 : ℕ) = 114688 + 4096 from rfl, countFrom_add, chunk18_28]
  rw [show (114688 : ℕ) = 110592 + 4096 from rfl, countFrom_add, chunk18_27]
  rw [show (110592 : ℕ) = 106496 + 4096 from rfl, countFrom_add, chunk18_26]
  rw [show (106496 : ℕ) = 102400 + 4096 from rfl, countFrom_add, chunk18_25]
  rw [show (102400 : ℕ) = 98304 + 4096 from rfl, countFrom_add, chunk18_24]
  rw [show (98304 : ℕ) = 94208 + 4096 from rfl, countFrom_add, chunk18_23]
  rw [show (94208 : ℕ) = 90112 + 4096 from rfl, countFrom_add, chunk18_22]
  rw [show (90112 : ℕ) = 86016 + 4096 from rfl, countFrom_add, chunk18_21]
  rw [show (86016 : ℕ) = 81920 + 4096 from rfl, countFrom_add, chunk18_20]
  rw [show (81920 : ℕ) = 77824 + 4096 from rfl, countFrom_add, chunk18_19]
  rw [show (77824 : ℕ) = 73728 + 4096 from rfl, countFrom_add, chunk18_18]
  rw [show (73728 : ℕ) = 69632 + 4096 from rfl, countFrom_add, chunk18_17]
  rw [show (69632 : ℕ) = 65536 + 4096 from rfl, countFrom_add, chunk18_16]
  rw [show (65536 : ℕ) = 61440 + 4096 from rfl, countFrom_add, chunk18_15]
  rw [show (61440 : ℕ) = 57344 + 4096 from rfl, countFrom_add, chunk18_14]
  rw [show (57344 : ℕ) = 53248 + 4096 from rfl, countFrom_add, chunk18_13]
  rw [show (53248 : ℕ) = 49152 + 4096 from rfl, countFrom_add, chunk18_12]
  rw [show (49152 : ℕ) = 45056 + 4096 from rfl, countFrom_add, chunk18_11]
  rw [show (45056 : ℕ) = 40960 + 4096 from rfl, countFrom_add, chunk18_10]
  rw [show (40960 : ℕ) = 36864 + 4096 from rfl, countFrom_add, chunk18_9]
  rw [show (36864 : ℕ) = 32768 + 4096 from rfl, countFrom_add, chunk18_8]
  rw [show (32768 : ℕ) = 28672 + 4096 from rfl, countFrom_add, chunk18_7]
  rw [show (28672 : ℕ) = 24576 + 4096 from rfl, countFrom_add, chunk18_6]
  rw [show (24576 : ℕ) = 20480 + 4096 from rfl, countFrom_add, chunk18_5]
  rw [show (20480 : ℕ) = 16384 + 4096 from rfl, countFrom_add, chunk18_4]
  rw [show (16384 : ℕ) = 12288 + 4096 from rfl, countFrom_add, chunk18_3]
  rw [show (12288 : ℕ) = 8192 + 4096 from rfl, countFrom_add, chunk18_2]
  rw [show (8192 : ℕ) = 4096 + 4096 from rfl, countFrom_add, chunk18_1]
  rw [show (4096 : ℕ) = 0 + 4096 from rfl, countFrom_add, chunk18_0]
  rfl

/-- **Density certificate** at level `18`: every `n ≥ 2^18` outside 7495 residue classes
mod `2^18` (density `7495/262144 < 2.86%`) has stopping time `≤ 36` for `C` (`≤ 18` for `Tt`). -/
theorem density_certificate_18 :
    (uncertified 18).card = 7495 ∧
    ∀ n, 2 ^ 18 ≤ n → n % 2 ^ 18 ∉ uncertified 18 →
      ∃ hs : HasStoppingTime n, stoppingTime n hs ≤ 36 := by
  refine ⟨?_, fun n hn hU => ?_⟩
  · rw [uncertified_card]; exact countFrom_18
  · have h : certB 18 (n % 2 ^ 18) = true := by
      by_contra hc
      exact hU (Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ (by positivity)),
        by simpa using hc⟩)
    exact stoppingTime_le_of_certB hn h

end APEX.Collatz

