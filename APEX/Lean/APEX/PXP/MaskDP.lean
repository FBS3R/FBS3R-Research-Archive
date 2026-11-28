/-
# A kernel-evaluable, proved-correct bit-mask dynamic programme for `g`

For a period `k`, trajectories `β : Traj k` are encoded by natural numbers `b < 2^k`
(`dec k b t = b.testBit t`) and flip sets by masks `f < 2^k` (`decF k f`).  The flip set of
`dec k b` is the mask `fl k b = b ^^^ rot k b` (`flips_dec`), compatibility is `c &&& b = 0`
(`compat_dec_iff`), and sums over `Traj k` become sums over `range (2^k)` (`sum_traj`).

`layer k n` is a table (a binary tree indexed by masks `S`) whose entry at `S` is the list of
values `g n (dec k c) (decF k S)` for the candidates `c` with `flips c ⊆ S` (in increasing
order).  Layer `n+1` is computed from layer `n` only, with list traversals and depth-`k` tree
look-ups, so the Lean kernel can evaluate it.

Main result: `M_eq_Mnat : M k n = Mnat k n` for every `k ≥ 1` and `n`, where
`Mnat k n` is the sum of the entry of `layer k n` at the full mask `2^k - 1`.
-/
import APEX.PXP.Main

namespace APEX.PXP
namespace MaskDP

open Finset

/-! ### Encodings -/

/-- The trajectory encoded by the bits of `b`. -/
def dec (k b : ℕ) : Traj k := fun t => b.testBit t.val

/-- The set of times encoded by the bits of `f`. -/
def decF (k f : ℕ) : Finset (Fin k) := univ.filter (fun t => f.testBit t.val = true)

/-- Cyclic rotation by one on `k` bits: bit `t` of `rot k b` is bit `t+1 (mod k)` of `b`. -/
def rot (k b : ℕ) : ℕ := (b >>> 1) ||| ((b &&& 1) <<< (k - 1))

/-- Flip mask. -/
def fl (k b : ℕ) : ℕ := b ^^^ rot k b

lemma testBit_ge {k x : ℕ} (hx : x < 2 ^ k) {t : ℕ} (ht : k ≤ t) : x.testBit t = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) ht))

lemma testBit_rot {k b : ℕ} (hb : b < 2 ^ k) {t : ℕ} (ht : t < k) :
    (rot k b).testBit t = b.testBit ((t + 1) % k) := by
  unfold rot
  simp only [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_and]
  by_cases h : t + 1 < k
  · rw [Nat.mod_eq_of_lt h]
    have : ¬ (t ≥ k - 1) := by omega
    simp [this, Nat.add_comm 1 t]
  · have e1 : t + 1 = k := by omega
    have e2 : (t + 1) % k = 0 := by rw [e1, Nat.mod_self]
    rw [e2, Nat.add_comm 1 t, e1, testBit_ge hb le_rfl]
    have : t - (k - 1) = 0 := by omega
    simp [this, show t ≥ k - 1 by omega, Nat.testBit_zero]

lemma rot_lt {k b : ℕ} (hb : b < 2 ^ k) : rot k b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  unfold rot
  simp only [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_and]
  rw [testBit_ge hb (by omega)]
  by_cases h0 : i - (k - 1) = 0
  · have : k = 0 := by omega
    subst this
    simp at hb; subst hb; simp
  · have : (1 : ℕ).testBit (i - (k - 1)) = false := by
      rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow]; simp; omega
    simp [this]

lemma fl_lt {k b : ℕ} (hb : b < 2 ^ k) : fl k b < 2 ^ k := Nat.xor_lt_two_pow hb (rot_lt hb)

lemma mem_decF {k f : ℕ} {t : Fin k} : t ∈ decF k f ↔ f.testBit t.val = true := by
  simp [decF]

lemma finRotate_val {k : ℕ} (t : Fin k) : (finRotate k t).val = (t.val + 1) % k := by
  cases k with
  | zero => exact t.elim0
  | succ m =>
    rw [coe_finRotate]
    split_ifs with h
    · subst h; simp
    · have : t.val < m := by
        have := t.isLt
        rcases Nat.lt_or_ge t.val m with h' | h'
        · exact h'
        · exact absurd (Fin.ext (by simp; omega)) h
      rw [Nat.mod_eq_of_lt (by omega)]

lemma flips_dec {k b : ℕ} (hb : b < 2 ^ k) : flips (dec k b) = decF k (fl k b) := by
  ext t
  rw [mem_flips, mem_decF, fl, Nat.testBit_xor, testBit_rot hb t.isLt]
  simp only [dec, finRotate_val]
  cases b.testBit t.val <;> cases b.testBit ((t.val + 1) % k) <;> simp

lemma decF_ext {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (h : ∀ t, t < k → a.testBit t = b.testBit t) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < k
  · exact h t ht
  · rw [testBit_ge ha (by omega), testBit_ge hb (by omega)]

lemma decF_subset_iff {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    decF k a ⊆ decF k b ↔ a &&& b = a := by
  constructor
  · intro h
    apply decF_ext (Nat.and_lt_two_pow _ hb) ha
    intro t ht
    have := @h ⟨t, ht⟩
    simp only [mem_decF] at this
    rw [Nat.testBit_and]
    cases hat : a.testBit t
    · simp
    · simp [this hat]
  · intro h t ht
    rw [mem_decF] at ht ⊢
    have := congrArg (fun x => x.testBit t.val) h
    simp only [Nat.testBit_and, ht] at this
    simpa using this

lemma decF_sdiff {k a b : ℕ} (h : a &&& b = a) :
    decF k b \ decF k a = decF k (b ^^^ a) := by
  ext t
  have e := congrArg (fun x => x.testBit t.val) h
  simp only [Nat.testBit_and] at e
  simp only [mem_sdiff, mem_decF, Nat.testBit_xor]
  cases hb : b.testBit t.val <;> cases ha : a.testBit t.val <;> simp_all

lemma decF_eq_empty_iff {k a : ℕ} (ha : a < 2 ^ k) : decF k a = ∅ ↔ a = 0 := by
  constructor
  · intro h
    apply decF_ext ha (by positivity)
    intro t ht
    have : (⟨t, ht⟩ : Fin k) ∉ decF k a := by rw [h]; simp
    rw [mem_decF] at this
    simpa using this
  · rintro rfl; ext t; simp [decF]

lemma decF_full (k : ℕ) : decF k (2 ^ k - 1) = univ := by
  ext t; simp [decF]

lemma compat_dec_iff {k b c : ℕ} (_hc : c < 2 ^ k) (hb : b < 2 ^ k) :
    Compat (dec k c) (dec k b) ↔ c &&& b = 0 := by
  constructor
  · intro h
    apply decF_ext (Nat.and_lt_two_pow _ hb) (by positivity)
    intro t ht
    have := h ⟨t, ht⟩
    simp only [dec] at this
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases h1 : c.testBit t <;> cases h2 : b.testBit t <;> simp_all
  · intro h t ⟨h1, h2⟩
    have := congrArg (fun x => x.testBit t.val) h
    simp only [Nat.testBit_and, Nat.zero_testBit] at this
    simp only [dec] at h1 h2
    rw [h1, h2] at this
    exact Bool.noConfusion this

lemma dec_injOn (k : ℕ) : Set.InjOn (dec k) (range (2 ^ k) : Set ℕ) := by
  intro a ha b hb h
  simp only [coe_range, Set.mem_Iio] at ha hb
  apply decF_ext ha hb
  intro t ht
  exact congrFun h ⟨t, ht⟩

lemma image_dec (k : ℕ) : (range (2 ^ k)).image (dec k) = univ := by
  apply eq_univ_of_card
  rw [card_image_of_injOn (dec_injOn k)]
  simp

lemma sum_traj {k : ℕ} {R : Type*} [AddCommMonoid R] (h : Traj k → R) :
    ∑ β : Traj k, h β = ∑ c ∈ range (2 ^ k), h (dec k c) := by
  rw [← sum_image (dec_injOn k), image_dec]

/-! ### Binary trees indexed by natural numbers (least significant bit first) -/

inductive BT (α : Type) where
  | leaf : α → BT α
  | node : BT α → BT α → BT α

def BT.get {α : Type} : BT α → ℕ → α
  | .leaf a, _ => a
  | .node l r, i => if i % 2 = 0 then l.get (i / 2) else r.get (i / 2)

def BT.build {α : Type} : ℕ → (ℕ → α) → BT α
  | 0, f => .leaf (f 0)
  | d + 1, f => .node (BT.build d (fun i => f (2 * i))) (BT.build d (fun i => f (2 * i + 1)))

lemma BT.get_build {α : Type} : ∀ (d : ℕ) (f : ℕ → α) (i : ℕ), i < 2 ^ d → (BT.build d f).get i = f i
  | 0, f, i, hi => by
    have : i = 0 := by simpa using hi
    subst this; rfl
  | d + 1, f, i, hi => by
    simp only [BT.build, BT.get]
    have hi2 : i / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    split_ifs with h
    · rw [BT.get_build d _ _ hi2]; congr 1; omega
    · rw [BT.get_build d _ _ hi2]; congr 1; omega

/-! ### The dynamic programme -/

/-- Candidates `c < 2^k` with `flips c ⊆ S`. -/
def candList (k S : ℕ) : List ℕ := (List.range (2 ^ k)).filter (fun c => fl k c &&& S == fl k c)

def candT (k : ℕ) : BT (List ℕ) := BT.build k (candList k)

def cand (k S : ℕ) : List ℕ := (candT k).get S

lemma cand_eq {k S : ℕ} (hS : S < 2 ^ k) : cand k S = candList k S := BT.get_build _ _ _ hS

/-- `∑ᵢ [cᵢ &&& b = 0] vᵢ` over two aligned lists. -/
def zsum (b : ℕ) : List ℕ → List ℕ → ℕ
  | c :: cs, v :: vs => (if c &&& b = 0 then v else 0) + zsum b cs vs
  | _, _ => 0

def val (k n : ℕ) (T : BT (List ℕ)) (f b : ℕ) : ℕ :=
  (if n = 0 ∧ f ^^^ fl k b = 0 then 1 else 0) + zsum b (cand k (f ^^^ fl k b)) (T.get (f ^^^ fl k b))

def step (k n : ℕ) (T : BT (List ℕ)) : BT (List ℕ) :=
  BT.build k (fun f => (cand k f).map (val k n T f))

def layer0 (k : ℕ) : BT (List ℕ) := BT.build k (fun f => (cand k f).map (fun _ => 0))

def layer (k n : ℕ) : BT (List ℕ) :=
  Nat.rec (motive := fun _ => BT (List ℕ)) (layer0 k) (fun n T => step k n T) n

/-- The value computed by the programme for `Tr Aₙ^k`. -/
def Mnat (k n : ℕ) : ℕ := ((layer k n).get (2 ^ k - 1)).sum

/-! ### Correctness -/

/-- `T` holds layer `n` of `g`. -/
def Rep (k n : ℕ) (T : BT (List ℕ)) : Prop :=
  ∀ S, S < 2 ^ k → T.get S = (cand k S).map (fun c => g n (dec k c) (decF k S))

lemma zsum_map (b : ℕ) (h : ℕ → ℕ) : ∀ l : List ℕ,
    zsum b l (l.map h) = (l.map (fun c => if c &&& b = 0 then h c else 0)).sum
  | [] => rfl
  | c :: l => by simp [zsum, zsum_map b h l]

lemma sum_filter_range (p : ℕ → Bool) (h : ℕ → ℕ) (N : ℕ) :
    (((List.range N).filter p).map h).sum = ∑ c ∈ range N, if p c then h c else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    by_cases hp : p N <;> simp [hp]

lemma mem_candList {k S c : ℕ} (h : c ∈ candList k S) : c < 2 ^ k ∧ fl k c &&& S = fl k c := by
  simp only [candList, List.mem_filter, List.mem_range, beq_iff_eq] at h
  exact h

lemma g_zero_of_not_cand {k n S c : ℕ} (hS : S < 2 ^ k) (hc : c < 2 ^ k)
    (h : ¬ (fl k c &&& S = fl k c)) : g n (dec k c) (decF k S) = 0 := by
  apply g_eq_zero_of_not_subset
  rw [flips_dec hc, decF_subset_iff (fl_lt hc) hS]
  exact h

/-- The sum over compatible predecessors, as computed by `zsum` from a correct layer. -/
lemma zsum_eq {k n S b : ℕ} (hS : S < 2 ^ k) (hb : b < 2 ^ k) :
    zsum b (cand k S) ((cand k S).map (fun c => g n (dec k c) (decF k S))) =
      ∑ β : Traj k, (if Compat β (dec k b) then g n β (decF k S) else 0) := by
  rw [zsum_map, cand_eq hS, candList, sum_filter_range, sum_traj]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  have hc' : c < 2 ^ k := mem_range.1 hc
  simp only [compat_dec_iff hc' hb]
  by_cases hp : fl k c &&& S = fl k c
  · simp [hp]
  · simp only [beq_iff_eq, hp, ↓reduceIte]
    split_ifs <;> simp [g_zero_of_not_cand hS hc' hp]

lemma step_rep {k n : ℕ} {T : BT (List ℕ)} (hT : Rep k n T) : Rep k (n + 1) (step k n T) := by
  intro f hf
  rw [step, BT.get_build _ _ _ hf]
  refine List.map_congr_left (fun b hb => ?_)
  rw [cand_eq hf] at hb
  obtain ⟨hb, hsub⟩ := mem_candList hb
  have hS : f ^^^ fl k b < 2 ^ k := Nat.xor_lt_two_pow hf (fl_lt hb)
  have hsub' : flips (dec k b) ⊆ decF k f := by
    rw [flips_dec hb, decF_subset_iff (fl_lt hb) hf]; exact hsub
  rw [val, hT _ hS, zsum_eq hS hb, g]
  simp only [hsub', ↓reduceIte]
  rw [flips_dec hb, decF_sdiff hsub, δ]
  simp only [decF_eq_empty_iff hS]

lemma layer0_rep (k : ℕ) : Rep k 0 (layer0 k) := by
  intro S hS
  rw [layer0, BT.get_build _ _ _ hS]
  rfl

lemma layer_rep (k : ℕ) : ∀ n, Rep k n (layer k n)
  | 0 => layer0_rep k
  | n + 1 => step_rep (layer_rep k n)

theorem M_eq_Mnat (k : ℕ) [NeZero k] (n : ℕ) : M k n = Mnat k n := by
  have hF : 2 ^ k - 1 < 2 ^ k := Nat.sub_lt (by positivity) one_pos
  rw [M_eq_sum_g, Mnat, layer_rep k n _ hF, ← decF_full k, sum_traj]
  rw [cand_eq hF, candList, sum_filter_range, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hc' : c < 2 ^ k := mem_range.1 ‹_›
  have : fl k c &&& (2 ^ k - 1) = fl k c := by
    apply decF_ext (Nat.and_lt_two_pow _ hF) (fl_lt hc')
    intro t ht; simp [ht]
  simp [this]

end MaskDP
end APEX.PXP
