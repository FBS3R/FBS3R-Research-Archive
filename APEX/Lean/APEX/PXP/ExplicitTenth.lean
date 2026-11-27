/-
# Explicit tenth moment generating function (kernel-checked for all `n`)

**Main theorem (`tenth_moment_gf`).**  For the Fibonacci-cube adjacency matrices `Aₙ`,
`(∑ₙ Tr Aₙ¹⁰ zⁿ) · (1 − z − z²)⁶ = P₅(z)` as formal power series over `ℤ`, where
`P₅ = 2z + 52z² + 3584z³ + 14656z⁴ + 135550z⁵ + 108284z⁶ + 681024z⁷ − 187752z⁸ + 839682z⁹
  − 662180z¹⁰ + 322900z¹¹ − 95200z¹² + 14560z¹³`.
Also `M10_vals`: `Tr Aₙ¹⁰` for `n = 0, …, 13`.

Method.  The traces are those of the proved-correct mask DP of `APEX.PXP.MaskDP`
(`M_eq_Mnat`).  For period `k = 10` a single kernel evaluation of the DP is too memory-hungry,
so the layers are *checkpointed*: the command `#pxp_mask_data` (ordinary meta code, untrusted)
adds literal tables `K10.PP` (candidates `b` with `flips b ⊆ S`, paired with `S ^^^ fl b`) and
`K10.T1 … K10.T12` (the DP layers).  Every table is then verified by the kernel in separate
`decide +kernel` lemmas (`cand_chk_*`, `bd*`, `step*_chk_*`), each recomputing one chunk of one
layer from the previous checkpoint.  The predecessor sums are computed on packed vectors
(`spk`, masked by `maskB`, summed by reduction modulo `2^40 − 1`); `packed_eq_zsum` proves this
agrees with `MaskDP.zsum`.  Combined with `pxp_moment_rational` (numerator degree `≤ 13`) the
fourteen values determine `P₅`.  Consistency: `P₅ ≡ 10! · z⁹ (mod 1 − z − z²)` as predicted by
`pxp_moment_residue`, and its top coefficient is `+14560`.
-/
import APEX.PXP.ExplicitHigher
import Mathlib.Tactic.Ring

set_option Elab.async false
set_option maxRecDepth 100000

namespace APEX.PXP
namespace MaskDP

open Finset

noncomputable section

/-! ### Kernel-friendly tree look-up and leaf decoding -/

/-- `BT.get` written with the raw recursor and primitive `Nat` operations. -/
def BT.getF {α : Type} (t : BT α) (i : ℕ) : α :=
  BT.rec (motive := fun _ => ℕ → α) (fun a _ => a)
    (fun _ _ gl gr i => bif Nat.beq (Nat.mod i 2) 0 then gl (Nat.div i 2) else gr (Nat.div i 2)) t i

lemma BT.getF_eq {α : Type} : ∀ (t : BT α) (i : ℕ), t.getF i = t.get i
  | .leaf _, _ => rfl
  | .node l r, i => by
    show (bif Nat.beq (i % 2) 0 then l.getF (i / 2) else r.getF (i / 2)) = _
    rw [BT.getF_eq l, BT.getF_eq r, BT.get]
    cases h : Nat.beq (i % 2) 0
    · rw [ite_cond_eq_false _ _ (eq_false (Nat.ne_of_beq_eq_false h))]; rfl
    · rw [ite_cond_eq_true _ _ (eq_true (Nat.eq_of_beq_eq_true h))]; rfl

/-! ### Packed vectors: `pkR w a N = ∑_{c<N} a c · 2^(w c)` -/

def pkR (w : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 ^ (w * N) * a N + pkR w a N

lemma pkR_lt {w : ℕ} {a : ℕ → ℕ} (ha : ∀ c, a c < 2 ^ w) : ∀ N, pkR w a N < 2 ^ (w * N)
  | 0 => by simp [pkR]
  | N + 1 => by
    have ih := pkR_lt ha N
    have h1 : a N + 1 ≤ 2 ^ w := ha N
    calc 2 ^ (w * N) * a N + pkR w a N < 2 ^ (w * N) * a N + 2 ^ (w * N) := by omega
      _ = 2 ^ (w * N) * (a N + 1) := by ring
      _ ≤ 2 ^ (w * N) * 2 ^ w := Nat.mul_le_mul_left _ h1
      _ = 2 ^ (w * (N + 1)) := by rw [← pow_add]; ring_nf

lemma testBit_pkR {w : ℕ} (hw : 0 < w) {a : ℕ → ℕ} (ha : ∀ c, a c < 2 ^ w) (j : ℕ) :
    ∀ N, (pkR w a N).testBit j = (decide (j / w < N) && (a (j / w)).testBit (j % w))
  | 0 => by simp [pkR]
  | N + 1 => by
    rw [pkR, Nat.testBit_two_pow_mul_add _ (pkR_lt ha N), testBit_pkR hw ha j N]
    have hj := Nat.div_add_mod j w
    split_ifs with h
    · have : j / w < N := (Nat.div_lt_iff_lt_mul hw).2 (by rw [Nat.mul_comm]; exact h)
      simp [this, show j / w < N + 1 by omega]
    · have hge : N ≤ j / w := (Nat.le_div_iff_mul_le hw).2 (by rw [Nat.mul_comm]; omega)
      by_cases hq : j / w = N
      · have : j - w * N = j % w := by rw [← hq]; omega
        rw [this, hq]; simp
      · have hgt : N + 1 ≤ j / w := by omega
        have h2 : (N + 1) * w ≤ j := (Nat.le_div_iff_mul_le hw).1 hgt
        have h3 : w ≤ j - w * N := by rw [Nat.add_mul] at h2; rw [Nat.mul_comm] at h2; omega
        rw [testBit_ge (ha N) h3]
        simp [show ¬ (j / w < N + 1) by omega]

lemma two_pow_modEq_one (w : ℕ) : 2 ^ w ≡ 1 [MOD 2 ^ w - 1] := by
  have h : 2 ^ w = (2 ^ w - 1) + 1 := by have := Nat.one_le_two_pow (n := w); omega
  show 2 ^ w % (2 ^ w - 1) = 1 % (2 ^ w - 1)
  have e : (2 ^ w - 1 + 1) % (2 ^ w - 1) = 1 % (2 ^ w - 1) := Nat.add_mod_left _ _
  rw [← h] at e
  exact e

lemma pkR_modEq (w : ℕ) (a : ℕ → ℕ) : ∀ N, pkR w a N ≡ ∑ c ∈ range N, a c [MOD 2 ^ w - 1]
  | 0 => by simp [pkR]; rfl
  | N + 1 => by
    rw [pkR, Finset.sum_range_succ, Nat.add_comm (∑ c ∈ range N, a c)]
    refine Nat.ModEq.add ?_ (pkR_modEq w a N)
    have : 2 ^ (w * N) ≡ 1 [MOD 2 ^ w - 1] := by
      rw [pow_mul]; simpa using (two_pow_modEq_one w).pow N
    simpa using this.mul_right (a N)

lemma pkR_mod {w : ℕ} {a : ℕ → ℕ} {N : ℕ} (h : ∑ c ∈ range N, a c < 2 ^ w - 1) :
    pkR w a N % (2 ^ w - 1) = ∑ c ∈ range N, a c := by
  rw [pkR_modEq w a N]; exact Nat.mod_eq_of_lt h

/-! ### Sparse packing -/

/-- `spk w cs vs = ⋁ᵢ vsᵢ · 2^(w csᵢ)`. -/
def spk (w : ℕ) (cs : List ℕ) : List ℕ → ℕ :=
  List.rec (motive := fun _ => List ℕ → ℕ) (fun _ => 0)
    (fun c _ ih vs => List.rec (motive := fun _ => ℕ) 0
      (fun v vs' _ => Nat.lor (Nat.shiftLeft v (Nat.mul w c)) (ih vs')) vs) cs

/-- The value attached to `x` in the aligned lists `cs`, `vs` (first match), or `0`. -/
def fieldOf : List ℕ → List ℕ → ℕ → ℕ
  | c :: cs, v :: vs, x => if x = c then v else fieldOf cs vs x
  | _, _, _ => 0

lemma fieldOf_lt {w : ℕ} : ∀ (cs vs : List ℕ), (∀ v ∈ vs, v < 2 ^ w) → ∀ x, fieldOf cs vs x < 2 ^ w
  | [], _, _, _ => by simp [fieldOf]
  | _ :: _, [], _, _ => by simp [fieldOf]
  | c :: cs, v :: vs, h, x => by
    simp only [fieldOf]
    split_ifs
    · exact h v (by simp)
    · exact fieldOf_lt cs vs (fun u hu => h u (by simp [hu])) x

lemma fieldOf_not_mem : ∀ (cs vs : List ℕ) (x : ℕ), x ∉ cs → fieldOf cs vs x = 0
  | [], _, _, _ => by simp [fieldOf]
  | _ :: _, [], _, _ => by simp [fieldOf]
  | c :: cs, v :: vs, x, hx => by
    simp only [List.mem_cons, not_or] at hx
    simp only [fieldOf, ite_cond_eq_false _ _ (eq_false hx.1)]
    exact fieldOf_not_mem cs vs x hx.2

lemma fieldOf_map (h : ℕ → ℕ) : ∀ (cs : List ℕ) (x : ℕ),
    fieldOf cs (cs.map h) x = if x ∈ cs then h x else 0
  | [], _ => by simp [fieldOf]
  | c :: cs, x => by
    simp only [List.map_cons, fieldOf, List.mem_cons]
    by_cases hx : x = c
    · subst hx; simp
    · rw [ite_cond_eq_false _ _ (eq_false hx), fieldOf_map h cs x]; simp [hx]

lemma testBit_spk {w : ℕ} (hw : 0 < w) (j : ℕ) : ∀ (cs vs : List ℕ), cs.Nodup →
    (∀ v ∈ vs, v < 2 ^ w) → (spk w cs vs).testBit j = (fieldOf cs vs (j / w)).testBit (j % w)
  | [], _, _, _ => by simp [spk, fieldOf]
  | _ :: _, [], _, _ => by simp [spk, fieldOf]
  | c :: cs, v :: vs, hnd, hv => by
    have hnd' := List.nodup_cons.1 hnd
    have hv' : ∀ u ∈ vs, u < 2 ^ w := fun u hu => hv u (by simp [hu])
    show ((v <<< (w * c)) ||| (spk w cs vs)).testBit j = _
    rw [Nat.testBit_or, testBit_spk hw j cs vs hnd'.2 hv', Nat.testBit_shiftLeft, fieldOf]
    have hj := Nat.div_add_mod j w
    by_cases hq : j / w = c
    · rw [ite_cond_eq_true _ _ (eq_true hq), hq, fieldOf_not_mem cs vs c hnd'.1, Nat.zero_testBit, Bool.or_false]
      have h1 : j ≥ w * c := by rw [← hq]; omega
      have h2 : j - w * c = j % w := by rw [← hq]; omega
      simp [h1, h2]
    · rw [ite_cond_eq_false _ _ (eq_false hq)]
      have : (decide (j ≥ w * c) && v.testBit (j - w * c)) = false := by
        by_cases h1 : j ≥ w * c
        · have hgt : c + 1 ≤ j / w := by
            have : c ≤ j / w := (Nat.le_div_iff_mul_le hw).2 (by rw [Nat.mul_comm]; exact h1)
            omega
          have h2 : (c + 1) * w ≤ j := (Nat.le_div_iff_mul_le hw).1 hgt
          have h3 : w ≤ j - w * c := by rw [Nat.add_mul] at h2; rw [Nat.mul_comm] at h2; omega
          rw [testBit_ge (hv v (by simp)) h3]; simp
        · simp [h1]
      rw [this, Bool.false_or]

lemma spk_eq_pkR {w N : ℕ} (hw : 0 < w) {cs vs : List ℕ} (hnd : cs.Nodup) (hv : ∀ v ∈ vs, v < 2 ^ w)
    (hcs : ∀ c ∈ cs, c < N) : spk w cs vs = pkR w (fieldOf cs vs) N := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_spk hw j cs vs hnd hv, testBit_pkR hw (fieldOf_lt cs vs hv) j N]
  by_cases h : j / w < N
  · simp [h]
  · rw [fieldOf_not_mem cs vs _ (fun hm => h (hcs _ hm))]; simp [h]

/-! ### Compatibility masks -/

def zmask (k w t : ℕ) : ℕ := pkR w (fun c => bif c.testBit t then 0 else 2 ^ w - 1) (2 ^ k)

def allm (k w : ℕ) : ℕ := pkR w (fun _ => 2 ^ w - 1) (2 ^ k)

def maskB (k w b : ℕ) : ℕ :=
  (List.range k).foldr (fun t acc => bif b.testBit t then Nat.land (zmask k w t) acc else acc) (allm k w)

lemma testBit_ones {w r : ℕ} (hr : r < w) : (2 ^ w - 1).testBit r = true := by simp [hr]

lemma testBit_maskB_aux {k w b j : ℕ} (hw : 0 < w) : ∀ L : List ℕ,
    (L.foldr (fun t acc => bif b.testBit t then Nat.land (zmask k w t) acc else acc) (allm k w)).testBit j
      = true ↔ (j / w < 2 ^ k ∧ ∀ t ∈ L, b.testBit t = true → (j / w).testBit t = false)
  | [] => by
    have hr := Nat.mod_lt j hw
    simp only [List.foldr_nil, allm]
    rw [testBit_pkR hw (fun _ => Nat.sub_lt (Nat.two_pow_pos w) one_pos) j, testBit_ones hr]
    simp
  | t :: L => by
    have hr := Nat.mod_lt j hw
    simp only [List.foldr_cons]
    have ih := testBit_maskB_aux (k := k) (w := w) (b := b) (j := j) hw L
    cases hbt : b.testBit t
    · simp only [Bool.cond_false, ih, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun s hs => hs.elim (fun e => by subst e; simp [hbt]) (h2 s)⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun s hs => h2 s (Or.inr hs)⟩
    · have hz : ∀ c : ℕ, (bif c.testBit t then 0 else 2 ^ w - 1) < 2 ^ w := fun c => by
        cases c.testBit t <;> simp
      simp only [Bool.cond_true]
      rw [show Nat.land (zmask k w t) _ = (zmask k w t) &&& _ from rfl, Nat.testBit_and,
        Bool.and_eq_true, ih, zmask, testBit_pkR hw hz j]
      simp only [List.mem_cons, Bool.and_eq_true, decide_eq_true_eq]
      cases hjt : (j / w).testBit t
      · simp only [Bool.cond_false, testBit_ones hr]
        constructor
        · rintro ⟨⟨h1, -⟩, h2, h3⟩
          exact ⟨h2, fun s hs _ => hs.elim (fun e => by subst e; exact hjt) (fun hs' => h3 s hs' ‹_›)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, by simp⟩, h1, fun s hs hb => h2 s (Or.inr hs) hb⟩
      · simp only [Bool.cond_true, Nat.zero_testBit]
        constructor
        · rintro ⟨⟨-, h⟩, -⟩; exact absurd h (by simp)
        · rintro ⟨-, h2⟩; have := h2 t (Or.inl rfl) hbt; rw [hjt] at this; exact absurd this (by simp)

lemma land_eq_zero_iff_bits {k c b : ℕ} (_hc : c < 2 ^ k) (hb : b < 2 ^ k) :
    c &&& b = 0 ↔ ∀ t < k, b.testBit t = true → c.testBit t = false := by
  constructor
  · intro h t _ hbt
    have := congrArg (fun x => x.testBit t) h
    simp only [Nat.testBit_and, Nat.zero_testBit, hbt, Bool.and_true] at this
    exact this
  · intro h
    apply decF_ext (Nat.and_lt_two_pow _ hb) (by positivity)
    intro t ht
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases hbt : b.testBit t
    · simp
    · simp [h t ht hbt]

/-- Masking a packed vector by `maskB` keeps exactly the fields `c` with `c &&& b = 0`. -/
lemma land_maskB {k w b : ℕ} (hw : 0 < w) (hb : b < 2 ^ k) {a : ℕ → ℕ} (ha : ∀ c, a c < 2 ^ w) :
    pkR w a (2 ^ k) &&& maskB k w b = pkR w (fun c => if c &&& b = 0 then a c else 0) (2 ^ k) := by
  have ha' : ∀ c, (if c &&& b = 0 then a c else 0) < 2 ^ w := fun c => by
    split_ifs
    · exact ha c
    · exact Nat.two_pow_pos w
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, testBit_pkR hw ha, testBit_pkR hw ha']
  have hm := testBit_maskB_aux (k := k) (w := w) (b := b) (j := j) hw (List.range k)
  rw [← maskB] at hm
  by_cases hq : j / w < 2 ^ k
  · have e : (∀ t ∈ List.range k, b.testBit t = true → (j / w).testBit t = false) ↔ j / w &&& b = 0 := by
      rw [land_eq_zero_iff_bits hq hb]; simp
    by_cases hz : j / w &&& b = 0
    · have : (maskB k w b).testBit j = true := hm.2 ⟨hq, e.2 hz⟩
      simp [hq, hz, this]
    · have : (maskB k w b).testBit j = false := by
        cases h' : (maskB k w b).testBit j
        · rfl
        · exact absurd (e.1 (hm.1 h').2) hz
      simp [hq, hz, this]
  · simp [hq]

/-! ### One layer step through packed vectors

`PP` holds, at leaf `S`, the candidates `b` (with `flips b ⊆ S`) paired with `S ^^^ fl k b`. -/

def candF (k S : ℕ) : List ℕ :=
  (List.range (2 ^ k)).filter (fun c => Nat.beq (Nat.land (fl k c) S) (fl k c))

lemma candF_eq (k S : ℕ) : candF k S = candList k S := rfl

def pairs (k S : ℕ) (l : List ℕ) : List (ℕ × ℕ) := l.map (fun b => (b, Nat.xor S (fl k b)))

def vtree (PP : BT (List (ℕ × ℕ))) (T : BT (List ℕ)) (k w : ℕ) : BT ℕ :=
  BT.build k (fun S => spk w ((PP.getF S).map Prod.fst) (T.getF S))

def mtree (k w : ℕ) : BT ℕ := BT.build k (maskB k w)

def valP (VT MT : BT ℕ) (w n : ℕ) (p : ℕ × ℕ) : ℕ :=
  Prod.rec (motive := fun _ => ℕ)
    (fun b S => Nat.add (bif Nat.beq n 0 && Nat.beq S 0 then 1 else 0)
      (Nat.mod (Nat.land (VT.getF S) (MT.getF b)) (2 ^ w - 1))) p

def leafP (PP : BT (List (ℕ × ℕ))) (VT MT : BT ℕ) (w n f : ℕ) : List ℕ :=
  (PP.getF f).map (valP VT MT w n)

def CandOK (PP : BT (List (ℕ × ℕ))) (k : ℕ) : Prop :=
  ∀ S, S < 2 ^ k → PP.get S = pairs k S (cand k S)

def chkCand (PP : BT (List (ℕ × ℕ))) (k a len : ℕ) : Bool :=
  (List.range' a len).all (fun S => PP.getF S == pairs k S (candF k S))

def chkBound (T : BT (List ℕ)) (k w : ℕ) : Bool :=
  (List.range' 0 (2 ^ k)).all (fun S => Nat.blt (T.getF S).sum (2 ^ w - 1))

def chkStep (PP : BT (List (ℕ × ℕ))) (T T' : BT (List ℕ)) (k w n a len : ℕ) : Bool :=
  (List.range' a len).all (fun S => leafP PP (vtree PP T k w) (mtree k w) w n S == T'.getF S)

lemma chkCand_append {PP : BT (List (ℕ × ℕ))} {k a l1 l2 : ℕ} (h1 : chkCand PP k a l1 = true)
    (h2 : chkCand PP k (a + l1) l2 = true) : chkCand PP k a (l1 + l2) = true := by
  unfold chkCand at *
  rw [← List.range'_append_1, List.all_append, h1, h2]; rfl

lemma chkStep_append {PP : BT (List (ℕ × ℕ))} {T T' : BT (List ℕ)} {k w n a l1 l2 : ℕ}
    (h1 : chkStep PP T T' k w n a l1 = true) (h2 : chkStep PP T T' k w n (a + l1) l2 = true) :
    chkStep PP T T' k w n a (l1 + l2) = true := by
  unfold chkStep at *
  rw [← List.range'_append_1, List.all_append, h1, h2]; rfl

lemma candOK_of_chk {PP : BT (List (ℕ × ℕ))} {k : ℕ} (h : chkCand PP k 0 (2 ^ k) = true) :
    CandOK PP k := by
  intro S hS
  unfold chkCand at h
  rw [List.all_eq_true] at h
  have := h S (by rw [List.mem_range'_1]; omega)
  rw [beq_iff_eq, BT.getF_eq] at this
  rw [this, cand_eq hS, candF_eq]

lemma bound_of_chk {T : BT (List ℕ)} {k w : ℕ} (h : chkBound T k w = true) {S : ℕ} (hS : S < 2 ^ k) :
    (T.get S).sum < 2 ^ w - 1 := by
  unfold chkBound at h
  rw [List.all_eq_true] at h
  have := h S (by rw [List.mem_range'_1]; omega)
  rw [Nat.blt_eq, BT.getF_eq] at this
  exact this

lemma le_sum_of_mem' : ∀ {l : List ℕ} {v : ℕ}, v ∈ l → v ≤ l.sum
  | _ :: l, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem' h; simp; omega

lemma nodup_candList (k S : ℕ) : (candList k S).Nodup := List.Pairwise.filter _ List.nodup_range

lemma mem_candList_iff {k S c : ℕ} : c ∈ candList k S ↔ c < 2 ^ k ∧ (fl k c &&& S == fl k c) = true := by
  simp [candList]

/-- The packed computation of the predecessor sum agrees with `zsum`. -/
lemma packed_eq_zsum {k w S b : ℕ} (hw : 0 < w) (hb : b < 2 ^ k) (h : ℕ → ℕ)
    (hbd : ((candList k S).map h).sum < 2 ^ w - 1) :
    (spk w (candList k S) ((candList k S).map h) &&& maskB k w b) % (2 ^ w - 1) =
      zsum b (candList k S) ((candList k S).map h) := by
  set cs := candList k S with hcs
  have hv : ∀ v ∈ cs.map h, v < 2 ^ w := fun v hv => by
    have := le_sum_of_mem' hv; omega
  have hlt : ∀ c, fieldOf cs (cs.map h) c < 2 ^ w := fieldOf_lt _ _ hv
  rw [spk_eq_pkR (N := 2 ^ k) hw (nodup_candList k S) hv (fun c hc => (mem_candList_iff.1 hc).1)]
  rw [land_maskB hw hb hlt]
  have key : ∀ c ∈ range (2 ^ k), (if c &&& b = 0 then fieldOf cs (cs.map h) c else 0) =
      if (fl k c &&& S == fl k c) = true then (if c &&& b = 0 then h c else 0) else 0 := by
    intro c hc
    rw [fieldOf_map]
    have hc' := mem_range.1 hc
    by_cases hp : (fl k c &&& S == fl k c) = true
    · have hm : c ∈ cs := mem_candList_iff.2 ⟨hc', hp⟩
      simp only [hm, hp, ↓reduceIte]
    · have hm : c ∉ cs := fun hm => hp (mem_candList_iff.1 hm).2
      simp [hm, hp]
  have hsum : ∑ c ∈ range (2 ^ k), (if c &&& b = 0 then fieldOf cs (cs.map h) c else 0) =
      zsum b cs (cs.map h) := by
    rw [Finset.sum_congr rfl key, zsum_map, hcs, candList, sum_filter_range]
  rw [pkR_mod, hsum]
  rw [hsum]
  calc zsum b cs (cs.map h) ≤ (cs.map h).sum := by
        rw [zsum_map]
        apply List.sum_le_sum
        intro c _
        split_ifs <;> omega
    _ < 2 ^ w - 1 := hbd

lemma valP_eq (VT MT : BT ℕ) (w n b S : ℕ) : valP VT MT w n (b, S) =
    (if n = 0 ∧ S = 0 then 1 else 0) + (VT.getF S &&& MT.getF b) % (2 ^ w - 1) := by
  show Nat.add (bif Nat.beq n 0 && Nat.beq S 0 then 1 else 0) _ = _
  congr 1
  by_cases h1 : n = 0 <;> by_cases h2 : S = 0 <;> simp [h1, h2]

lemma leafP_eq {PP : BT (List (ℕ × ℕ))} {T : BT (List ℕ)} {k w n f : ℕ} (hw : 0 < w)
    (hC : CandOK PP k) (hT : Rep k n T) (hB : chkBound T k w = true) (hf : f < 2 ^ k) :
    leafP PP (vtree PP T k w) (mtree k w) w n f =
      (cand k f).map (fun c => g (n + 1) (dec k c) (decF k f)) := by
  rw [← step_rep hT f hf, step, BT.get_build _ _ _ hf, leafP, BT.getF_eq, hC f hf, pairs,
    List.map_map]
  refine List.map_congr_left (fun b hb => ?_)
  rw [cand_eq hf] at hb
  obtain ⟨hb, -⟩ := mem_candList hb
  have hS : f ^^^ fl k b < 2 ^ k := Nat.xor_lt_two_pow hf (fl_lt hb)
  have hbd := bound_of_chk hB hS
  rw [hT _ hS, cand_eq hS] at hbd
  simp only [Function.comp_apply]
  rw [valP_eq, val]
  simp only [show Nat.xor f (fl k b) = f ^^^ fl k b from rfl]
  simp only [vtree, mtree, BT.getF_eq]
  rw [BT.get_build _ _ _ hS, BT.get_build _ _ _ hb, hC _ hS, hT _ hS, cand_eq hS, pairs,
    List.map_map]
  have : ∀ S : ℕ, (Prod.fst ∘ fun b' => (b', Nat.xor S (fl k b'))) = id := fun S => by funext x; rfl
  rw [this, List.map_id, packed_eq_zsum hw hb _ hbd]

lemma rep_next {PP : BT (List (ℕ × ℕ))} {T T' : BT (List ℕ)} {k w n : ℕ} (hw : 0 < w)
    (hC : CandOK PP k) (hT : Rep k n T) (hB : chkBound T k w = true)
    (h : chkStep PP T T' k w n 0 (2 ^ k) = true) : Rep k (n + 1) T' := by
  intro S hS
  unfold chkStep at h
  rw [List.all_eq_true] at h
  have := h S (by rw [List.mem_range'_1]; omega)
  rw [beq_iff_eq, BT.getF_eq] at this
  rw [← this, leafP_eq hw hC hT hB hS]

/-- Zero layer built from the candidate table. -/
def zeroT (PP : BT (List (ℕ × ℕ))) (k : ℕ) : BT (List ℕ) :=
  BT.build k (fun S => (PP.getF S).map (fun _ => 0))

lemma rep_zeroT {PP : BT (List (ℕ × ℕ))} {k : ℕ} (hC : CandOK PP k) : Rep k 0 (zeroT PP k) := by
  intro S hS
  rw [zeroT, BT.get_build _ _ _ hS, BT.getF_eq, hC S hS, pairs, List.map_map]
  rfl

lemma M_of_rep {T : BT (List ℕ)} {k n : ℕ} [NeZero k] (hT : Rep k n T) :
    M k n = ((T.getF (2 ^ k - 1)).sum : ℕ) := by
  have hF : 2 ^ k - 1 < 2 ^ k := Nat.sub_lt (by positivity) one_pos
  rw [M_eq_Mnat, Mnat, layer_rep k n _ hF, BT.getF_eq, hT _ hF]

lemma M_succ_of_rep {PP : BT (List (ℕ × ℕ))} {T : BT (List ℕ)} {k w n : ℕ} [NeZero k] (hw : 0 < w)
    (hC : CandOK PP k) (hT : Rep k n T) (hB : chkBound T k w = true) :
    M k (n + 1) = ((leafP PP (vtree PP T k w) (mtree k w) w n (2 ^ k - 1)).sum : ℕ) := by
  have hF : 2 ^ k - 1 < 2 ^ k := Nat.sub_lt (by positivity) one_pos
  rw [M_eq_Mnat, Mnat, layer_rep k (n + 1) _ hF, leafP_eq hw hC hT hB hF]

end

end MaskDP
end APEX.PXP

/-! ### Certificate generation (untrusted; every generated table is checked by the kernel below) -/

namespace APEX.PXP.MaskDP.Gen

open Lean Elab Command

def flN (k b : Nat) : Nat := b ^^^ ((b >>> 1) ||| ((b &&& 1) <<< (k - 1)))

def candsN (k : Nat) : Array (Array Nat) :=
  let K := 2 ^ k
  let fls := (Array.range K).map (flN k)
  (Array.range K).map fun S => (Array.range K).filter fun c => (fls[c]! &&& S) == fls[c]!

def stepN (k n : Nat) (cand : Array (Array Nat)) (T : Array (Array Nat)) : Array (Array Nat) :=
  (Array.range (2 ^ k)).map fun f => (cand[f]!).map fun b => Id.run do
    let S := f ^^^ flN k b
    let cs := cand[S]!
    let vs := T[S]!
    let mut acc := if n == 0 && S == 0 then 1 else 0
    for i in [0:cs.size] do
      if cs[i]! &&& b == 0 then acc := acc + vs[i]!
    return acc

def listE (ty : Expr) (l : List Expr) : Expr :=
  l.foldr (fun a acc => mkApp3 (mkConst ``List.cons [levelZero]) ty a acc)
    (mkApp (mkConst ``List.nil [levelZero]) ty)

def treeE (ty : Expr) (leaf : Nat → Expr) : Nat → Nat → Nat → Expr
  | 0, off, _ => mkApp2 (mkConst ``BT.leaf) ty (leaf off)
  | d + 1, off, st => mkApp3 (mkConst ``BT.node) ty (treeE ty leaf d off (2 * st))
      (treeE ty leaf d (off + st) (2 * st))

def addDataDef (name : Name) (ty val : Expr) : CoreM Unit := do
  let dv : DefinitionVal :=
    { name := name, levelParams := [], type := ty, value := val,
      hints := ReducibilityHints.regular 1, safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl dv)

/-- `#pxp_mask_data NS k N` adds `NS.PP` (candidate/predecessor table) and the layers
`NS.T1, …, NS.T(N-1)` of the mask DP, as plain literal data. -/
elab "#pxp_mask_data " ns:ident kk:num NN:num : command => do
  let k := kk.getNat
  let N := NN.getNat
  let cand := candsN k
  let natT := mkConst ``Nat
  let pairT := mkApp2 (mkConst ``Prod [levelZero, levelZero]) natT natT
  let lpT := mkApp (mkConst ``List [levelZero]) pairT
  let lnT := mkApp (mkConst ``List [levelZero]) natT
  let ppE := treeE lpT (fun S => listE pairT ((cand[S]!).toList.map fun b =>
      mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) natT natT (mkRawNatLit b)
        (mkRawNatLit (S ^^^ flN k b)))) k 0 1
  liftCoreM <| addDataDef (ns.getId ++ `PP) (mkApp (mkConst ``BT) lpT) ppE
  let mut T := cand.map (fun c => c.map fun _ => 0)
  for n in [0:N-1] do
    T := stepN k n cand T
    let T' := T
    let tE := treeE lnT (fun S => listE natT ((T'[S]!).toList.map mkRawNatLit)) k 0 1
    liftCoreM <| addDataDef (ns.getId ++ Name.mkSimple s!"T{n+1}") (mkApp (mkConst ``BT) lnT) tE

end APEX.PXP.MaskDP.Gen

#pxp_mask_data APEX.PXP.MaskDP.K10 10 13

namespace APEX.PXP
namespace MaskDP
namespace K10

theorem cand_chk_0 : chkCand PP 10 0 98 = true := by decide +kernel
theorem cand_chk_1 : chkCand PP 10 98 98 = true := by decide +kernel
theorem cand_chk_2 : chkCand PP 10 196 98 = true := by decide +kernel
theorem cand_chk_3 : chkCand PP 10 294 98 = true := by decide +kernel
theorem cand_chk_4 : chkCand PP 10 392 98 = true := by decide +kernel
theorem cand_chk_5 : chkCand PP 10 490 98 = true := by decide +kernel
theorem cand_chk_6 : chkCand PP 10 588 98 = true := by decide +kernel
theorem cand_chk_7 : chkCand PP 10 686 98 = true := by decide +kernel
theorem cand_chk_8 : chkCand PP 10 784 98 = true := by decide +kernel
theorem cand_chk_9 : chkCand PP 10 882 98 = true := by decide +kernel
theorem cand_chk_10 : chkCand PP 10 980 44 = true := by decide +kernel
theorem cand_chk : chkCand PP 10 0 (2 ^ 10) = true := by
  have h1 := chkCand_append cand_chk_0 cand_chk_1
  have h2 := chkCand_append h1 cand_chk_2
  have h3 := chkCand_append h2 cand_chk_3
  have h4 := chkCand_append h3 cand_chk_4
  have h5 := chkCand_append h4 cand_chk_5
  have h6 := chkCand_append h5 cand_chk_6
  have h7 := chkCand_append h6 cand_chk_7
  have h8 := chkCand_append h7 cand_chk_8
  have h9 := chkCand_append h8 cand_chk_9
  have h10 := chkCand_append h9 cand_chk_10
  exact h10

theorem C_ok : CandOK PP 10 := candOK_of_chk cand_chk

noncomputable def T0 : BT (List ℕ) := zeroT PP 10

theorem rep0 : Rep 10 0 T0 := rep_zeroT C_ok

theorem bd0 : chkBound T0 10 40 = true := by decide +kernel
theorem bd1 : chkBound T1 10 40 = true := by decide +kernel
theorem bd2 : chkBound T2 10 40 = true := by decide +kernel
theorem bd3 : chkBound T3 10 40 = true := by decide +kernel
theorem bd4 : chkBound T4 10 40 = true := by decide +kernel
theorem bd5 : chkBound T5 10 40 = true := by decide +kernel
theorem bd6 : chkBound T6 10 40 = true := by decide +kernel
theorem bd7 : chkBound T7 10 40 = true := by decide +kernel
theorem bd8 : chkBound T8 10 40 = true := by decide +kernel
theorem bd9 : chkBound T9 10 40 = true := by decide +kernel
theorem bd10 : chkBound T10 10 40 = true := by decide +kernel
theorem bd11 : chkBound T11 10 40 = true := by decide +kernel
theorem bd12 : chkBound T12 10 40 = true := by decide +kernel

theorem step0_chk_0 : chkStep PP T0 T1 10 40 0 0 752 = true := by decide +kernel
theorem step0_chk_1 : chkStep PP T0 T1 10 40 0 752 272 = true := by decide +kernel
theorem step0_chk : chkStep PP T0 T1 10 40 0 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step0_chk_0 step0_chk_1
  exact h1

theorem rep1 : Rep 10 1 T1 := rep_next (by norm_num) C_ok rep0 bd0 step0_chk

theorem step1_chk_0 : chkStep PP T1 T2 10 40 1 0 752 = true := by decide +kernel
theorem step1_chk_1 : chkStep PP T1 T2 10 40 1 752 272 = true := by decide +kernel
theorem step1_chk : chkStep PP T1 T2 10 40 1 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step1_chk_0 step1_chk_1
  exact h1

theorem rep2 : Rep 10 2 T2 := rep_next (by norm_num) C_ok rep1 bd1 step1_chk

theorem step2_chk_0 : chkStep PP T2 T3 10 40 2 0 752 = true := by decide +kernel
theorem step2_chk_1 : chkStep PP T2 T3 10 40 2 752 272 = true := by decide +kernel
theorem step2_chk : chkStep PP T2 T3 10 40 2 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step2_chk_0 step2_chk_1
  exact h1

theorem rep3 : Rep 10 3 T3 := rep_next (by norm_num) C_ok rep2 bd2 step2_chk

theorem step3_chk_0 : chkStep PP T3 T4 10 40 3 0 752 = true := by decide +kernel
theorem step3_chk_1 : chkStep PP T3 T4 10 40 3 752 272 = true := by decide +kernel
theorem step3_chk : chkStep PP T3 T4 10 40 3 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step3_chk_0 step3_chk_1
  exact h1

theorem rep4 : Rep 10 4 T4 := rep_next (by norm_num) C_ok rep3 bd3 step3_chk

theorem step4_chk_0 : chkStep PP T4 T5 10 40 4 0 752 = true := by decide +kernel
theorem step4_chk_1 : chkStep PP T4 T5 10 40 4 752 272 = true := by decide +kernel
theorem step4_chk : chkStep PP T4 T5 10 40 4 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step4_chk_0 step4_chk_1
  exact h1

theorem rep5 : Rep 10 5 T5 := rep_next (by norm_num) C_ok rep4 bd4 step4_chk

theorem step5_chk_0 : chkStep PP T5 T6 10 40 5 0 752 = true := by decide +kernel
theorem step5_chk_1 : chkStep PP T5 T6 10 40 5 752 272 = true := by decide +kernel
theorem step5_chk : chkStep PP T5 T6 10 40 5 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step5_chk_0 step5_chk_1
  exact h1

theorem rep6 : Rep 10 6 T6 := rep_next (by norm_num) C_ok rep5 bd5 step5_chk

theorem step6_chk_0 : chkStep PP T6 T7 10 40 6 0 752 = true := by decide +kernel
theorem step6_chk_1 : chkStep PP T6 T7 10 40 6 752 272 = true := by decide +kernel
theorem step6_chk : chkStep PP T6 T7 10 40 6 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step6_chk_0 step6_chk_1
  exact h1

theorem rep7 : Rep 10 7 T7 := rep_next (by norm_num) C_ok rep6 bd6 step6_chk

theorem step7_chk_0 : chkStep PP T7 T8 10 40 7 0 752 = true := by decide +kernel
theorem step7_chk_1 : chkStep PP T7 T8 10 40 7 752 272 = true := by decide +kernel
theorem step7_chk : chkStep PP T7 T8 10 40 7 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step7_chk_0 step7_chk_1
  exact h1

theorem rep8 : Rep 10 8 T8 := rep_next (by norm_num) C_ok rep7 bd7 step7_chk

theorem step8_chk_0 : chkStep PP T8 T9 10 40 8 0 752 = true := by decide +kernel
theorem step8_chk_1 : chkStep PP T8 T9 10 40 8 752 272 = true := by decide +kernel
theorem step8_chk : chkStep PP T8 T9 10 40 8 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step8_chk_0 step8_chk_1
  exact h1

theorem rep9 : Rep 10 9 T9 := rep_next (by norm_num) C_ok rep8 bd8 step8_chk

theorem step9_chk_0 : chkStep PP T9 T10 10 40 9 0 752 = true := by decide +kernel
theorem step9_chk_1 : chkStep PP T9 T10 10 40 9 752 272 = true := by decide +kernel
theorem step9_chk : chkStep PP T9 T10 10 40 9 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step9_chk_0 step9_chk_1
  exact h1

theorem rep10 : Rep 10 10 T10 := rep_next (by norm_num) C_ok rep9 bd9 step9_chk

theorem step10_chk_0 : chkStep PP T10 T11 10 40 10 0 752 = true := by decide +kernel
theorem step10_chk_1 : chkStep PP T10 T11 10 40 10 752 272 = true := by decide +kernel
theorem step10_chk : chkStep PP T10 T11 10 40 10 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step10_chk_0 step10_chk_1
  exact h1

theorem rep11 : Rep 10 11 T11 := rep_next (by norm_num) C_ok rep10 bd10 step10_chk

theorem step11_chk_0 : chkStep PP T11 T12 10 40 11 0 752 = true := by decide +kernel
theorem step11_chk_1 : chkStep PP T11 T12 10 40 11 752 272 = true := by decide +kernel
theorem step11_chk : chkStep PP T11 T12 10 40 11 0 (2 ^ 10) = true := by
  have h1 := chkStep_append step11_chk_0 step11_chk_1
  exact h1

theorem rep12 : Rep 10 12 T12 := rep_next (by norm_num) C_ok rep11 bd11 step11_chk

theorem M_0 : M 10 0 = 0 := by
  rw [M_of_rep rep0]
  have : (T0.getF (2 ^ 10 - 1)).sum = 0 := by decide +kernel
  rw [this]; rfl

theorem M_1 : M 10 1 = 2 := by
  rw [M_of_rep rep1]
  have : (T1.getF (2 ^ 10 - 1)).sum = 2 := by decide +kernel
  rw [this]; rfl

theorem M_2 : M 10 2 = 64 := by
  rw [M_of_rep rep2]
  have : (T2.getF (2 ^ 10 - 1)).sum = 64 := by decide +kernel
  rw [this]; rfl

theorem M_3 : M 10 3 = 3950 := by
  rw [M_of_rep rep3]
  have : (T3.getF (2 ^ 10 - 1)).sum = 3950 := by decide +kernel
  rw [this]; rfl

theorem M_4 : M 10 4 = 37760 := by
  rw [M_of_rep rep4]
  have : (T4.getF (2 ^ 10 - 1)).sum = 37760 := by decide +kernel
  rw [this]; rfl

theorem M_5 : M 10 5 = 325980 := by
  rw [M_of_rep rep5]
  have : (T5.getF (2 ^ 10 - 1)).sum = 325980 := by decide +kernel
  rw [this]; rfl

theorem M_6 : M 10 6 = 1686756 := by
  rw [M_of_rep rep6]
  have : (T6.getF (2 ^ 10 - 1)).sum = 1686756 := by decide +kernel
  rw [this]; rfl

theorem M_7 : M 10 7 = 7608942 := by
  rw [M_of_rep rep7]
  have : (T7.getF (2 ^ 10 - 1)).sum = 7608942 := by decide +kernel
  rw [this]; rfl

theorem M_8 : M 10 8 = 28179160 := by
  rw [M_of_rep rep8]
  have : (T8.getF (2 ^ 10 - 1)).sum = 28179160 := by decide +kernel
  rw [this]; rfl

theorem M_9 : M 10 9 = 94410290 := by
  rw [M_of_rep rep9]
  have : (T9.getF (2 ^ 10 - 1)).sum = 94410290 := by decide +kernel
  rw [this]; rfl

theorem M_10 : M 10 10 = 287086340 := by
  rw [M_of_rep rep10]
  have : (T10.getF (2 ^ 10 - 1)).sum = 287086340 := by decide +kernel
  rw [this]; rfl

theorem M_11 : M 10 11 = 816272908 := by
  rw [M_of_rep rep11]
  have : (T11.getF (2 ^ 10 - 1)).sum = 816272908 := by decide +kernel
  rw [this]; rfl

theorem M_12 : M 10 12 = 2190749576 := by
  rw [M_of_rep rep12]
  have : (T12.getF (2 ^ 10 - 1)).sum = 2190749576 := by decide +kernel
  rw [this]; rfl

theorem M_13 : M 10 13 = 5616610010 := by
  rw [M_succ_of_rep (by norm_num) C_ok rep12 bd12]
  have : (leafP PP (vtree PP T12 10 40) (mtree 10 40) 40 12 (2 ^ 10 - 1)).sum = 5616610010 := by decide +kernel
  rw [this]; rfl

end K10
end MaskDP
end APEX.PXP

namespace APEX.PXP

open PowerSeries

/-- `Tr Aₙ¹⁰` for `n = 0, …, 13`. -/
theorem M10_vals : M 10 0 = 0 ∧ M 10 1 = 2 ∧ M 10 2 = 64 ∧ M 10 3 = 3950 ∧ M 10 4 = 37760 ∧
    M 10 5 = 325980 ∧ M 10 6 = 1686756 ∧ M 10 7 = 7608942 ∧ M 10 8 = 28179160 ∧
    M 10 9 = 94410290 ∧ M 10 10 = 287086340 ∧ M 10 11 = 816272908 ∧ M 10 12 = 2190749576 ∧
    M 10 13 = 5616610010 :=
  ⟨MaskDP.K10.M_0, MaskDP.K10.M_1, MaskDP.K10.M_2, MaskDP.K10.M_3, MaskDP.K10.M_4,
    MaskDP.K10.M_5, MaskDP.K10.M_6, MaskDP.K10.M_7, MaskDP.K10.M_8, MaskDP.K10.M_9,
    MaskDP.K10.M_10, MaskDP.K10.M_11, MaskDP.K10.M_12, MaskDP.K10.M_13⟩

theorem tenth_moment_gf :
    PowerSeries.mk (fun n => M 10 n) * (1 - X - X ^ 2) ^ 6 =
      ((2 * Polynomial.X + 52 * Polynomial.X ^ 2 + 3584 * Polynomial.X ^ 3
        + 14656 * Polynomial.X ^ 4 + 135550 * Polynomial.X ^ 5 + 108284 * Polynomial.X ^ 6
        + 681024 * Polynomial.X ^ 7 - 187752 * Polynomial.X ^ 8 + 839682 * Polynomial.X ^ 9
        - 662180 * Polynomial.X ^ 10 + 322900 * Polynomial.X ^ 11 - 95200 * Polynomial.X ^ 12
        + 14560 * Polynomial.X ^ 13 : Polynomial ℤ) : PowerSeries ℤ) := by
  have e := numerator_eq 5 (by norm_num)
    (2 * Polynomial.X + 52 * Polynomial.X ^ 2 + 3584 * Polynomial.X ^ 3
        + 14656 * Polynomial.X ^ 4 + 135550 * Polynomial.X ^ 5 + 108284 * Polynomial.X ^ 6
        + 681024 * Polynomial.X ^ 7 - 187752 * Polynomial.X ^ 8 + 839682 * Polynomial.X ^ 9
        - 662180 * Polynomial.X ^ 10 + 322900 * Polynomial.X ^ 11 - 95200 * Polynomial.X ^ 12
        + 14560 * Polynomial.X ^ 13)
  simp only [show 2 * 5 = 10 by rfl, show 5 + 1 = 6 by rfl] at e
  apply e
  · compute_degree!
  · intro n hn
    set S := PowerSeries.mk (fun n => M 10 n) with hS
    have hD : S * (1 - X - X ^ 2) ^ 6 =
        X ^ 0 * S - 6 * (X ^ 1 * S) + 9 * (X ^ 2 * S) + 10 * (X ^ 3 * S) - 30 * (X ^ 4 * S)
        - 6 * (X ^ 5 * S) + 41 * (X ^ 6 * S) + 6 * (X ^ 7 * S) - 30 * (X ^ 8 * S)
        - 10 * (X ^ 9 * S) + 9 * (X ^ 10 * S) + 6 * (X ^ 11 * S) + X ^ 12 * S := by ring
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := M10_vals
    rw [hD]
    simp only [map_sub, map_add, hS, coeff_X_pow_mul_mk]
    norm_num at hn
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      coeff_X_pow_mul_mk, Polynomial.coeff_X_pow, Polynomial.coeff_X]

end APEX.PXP

