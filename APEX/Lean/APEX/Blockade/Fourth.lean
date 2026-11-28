import APEX.Blockade.Moments

/-!
# Range-`r` blockade: the fourth spectral moment

**Main theorem (`fourth_moment r : Conj4 r`, every `r : ℕ`, including `r = 0`).**
`(∑ₙ Tr A_{n,r}⁴ zⁿ) · (1 − z − z^{r+1})³ = 2z·D_r + 4z²(1 + … + z^{r−1})·D_r + 24 z^{r+2}`
as formal power series over `ℤ`, where `A_{n,r} = adjMat r n` (Moments.lean).

Proof structure:
* `trace_pow_eq_sum_Wl`: `Tr A^k` counts closed index sequences of admissible single flips.
* `trace_four_decomp`: closed 4-walks are `i i j j`, `i j j i`, `i j i j`, giving
  `Tr A⁴ = Σ_u deg u + 3·Σ_{u, i≠j}[u^i][u^j][u^{ij}] + 2·Σ_{u, i≠j}[u^i][u^j](1 − [u^{ij}])`.
* `Q_total`: the square term equals `4 Σ_u κ(u)(κ(u) − 1)` (`κ` = number of `1`s), via the
  involutions `u ↦ u^i`, `u ↦ u^j` (`q_pair`).
* `nf_pair` + `card_zero_block`: the non-closing cherries at `i ≠ j` exist iff `|i − j| ≤ r` and
  `u` vanishes on the union of the two `r`-windows; their number is `a(min − r)·a(n − 1 − max − r)`.
* `trace_four_eq`: `Tr A⁴ = 2eₙ + 12 s₂(n) + 2 hN(n)`, and the series
  `E·D² = z` (Moments), `S₂·D³ = 2z^{r+2}` (`series_s2_cube`, from `s2_rec`),
  `H·D² = 2z²(1 + … + z^{r−1})` (`series_hN_sq`, with `Fser·D = 1` from `ident_a`).
-/

namespace APEX.Blockade

open Finset

/-! ### Flip calculus -/

lemma getD_flip {w : List Bool} {i : ℕ} (h : i < w.length) (t : ℕ) :
    (flip w i).getD t false = if t = i then !(w.getD i false) else w.getD t false := by
  split_ifs with ht
  · subst ht; exact getD_flip_self h
  · exact getD_flip_ne w (Ne.symm ht)

lemma ext_getD {l₁ l₂ : List Bool} (h : l₁.length = l₂.length)
    (h' : ∀ t, l₁.getD t false = l₂.getD t false) : l₁ = l₂ := by
  apply List.ext_getElem?
  intro t
  have := h' t
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
  rcases Nat.lt_or_ge t l₁.length with ht | ht
  · rw [List.getElem?_eq_getElem ht, List.getElem?_eq_getElem (h ▸ ht)] at this ⊢
    simpa using this
  · rw [List.getElem?_eq_none ht, List.getElem?_eq_none (h ▸ ht)]

lemma flip_comm {w : List Bool} {i j : ℕ} (hi : i < w.length) (hj : j < w.length) :
    flip (flip w i) j = flip (flip w j) i := by
  apply ext_getD (by simp [length_flip])
  intro t
  simp only [getD_flip, length_flip, hi, hj]
  by_cases h1 : t = i <;> by_cases h2 : t = j <;> by_cases h3 : i = j <;> simp_all

/-- `0/1` indicator that flipping position `i` keeps admissibility. -/
def fl (r : ℕ) (w : List Bool) (i : ℕ) : ℤ := if Adm r (flip w i) then 1 else 0

/-- Degree of a vertex. -/
def dg (r n : ℕ) (w : List Bool) : ℤ := ∑ i ∈ range n, fl r w i

lemma fl_mul_self (r : ℕ) (w : List Bool) (i : ℕ) : fl r w i * fl r w i = fl r w i := by
  unfold fl; split_ifs <;> simp

/-! ### Walk counts -/

/-- `Wl r n k x y`: number of index sequences `(i₁,…,i_k)` in `range n` leading from `x` to `y`
through admissible words by single flips. -/
def Wl (r n : ℕ) : ℕ → List Bool → List Bool → ℤ
  | 0, x, y => if x = y then 1 else 0
  | k + 1, x, y => ∑ i ∈ range n, if Adm r (flip x i) then Wl r n k (flip x i) y else 0

lemma sum_adj (r n : ℕ) (u : V r n) (φ : List Bool → ℤ) :
    ∑ v : V r n, adjMat r n u v * φ v.1 =
      ∑ i ∈ range n, if Adm r (flip u.1 i) then φ (flip u.1 i) else 0 := by
  have hu := mem_C.1 u.2
  simp only [adjMat, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [← sum_filter, ← sum_filter]
  symm
  apply sum_bij (fun i hi => (⟨flip u.1 i, mem_C.2 ⟨by rw [length_flip, hu.1],
    (mem_filter.1 hi).2⟩⟩ : V r n))
  · intro i hi
    rw [mem_filter] at hi ⊢
    exact ⟨mem_univ _, i, by rw [hu.1]; exact hi.1, rfl⟩
  · intro i hi j hj h
    have := congrArg Subtype.val h
    exact flip_inj (by rw [hu.1]; exact mem_range.1 (mem_filter.1 hi).1) this
  · intro v hv
    obtain ⟨-, i, hi, hv⟩ := mem_filter.1 hv
    rw [hu.1] at hi
    refine ⟨i, mem_filter.2 ⟨hi, ?_⟩, Subtype.ext hv.symm⟩
    rw [← hv]; exact (mem_C.1 v.2).2
  · intro i hi; rfl

lemma pow_apply_eq_Wl (r n k : ℕ) (u v : V r n) : (adjMat r n ^ k) u v = Wl r n k u.1 v.1 := by
  induction k generalizing u with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Wl]
    by_cases h : u = v
    · simp [h]
    · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'))]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    rw [sum_adj r n u (fun x => Wl r n k x v.1)]
    rfl

theorem trace_pow_eq_sum_Wl (r n k : ℕ) :
    Matrix.trace (adjMat r n ^ k) = ∑ w ∈ C r n, Wl r n k w w := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, pow_apply_eq_Wl]
  rw [univ_eq_attach]
  exact sum_attach (C r n) (fun w => Wl r n k w w)

/-! ### Short walks back to the start -/

lemma flip_flip_ne {y : List Bool} {k l : ℕ} (hk : k < y.length) (hkl : l ≠ k) :
    flip (flip y k) l ≠ y := by
  intro h
  have : (flip (flip y k) l).getD k false = y.getD k false := by rw [h]
  rw [getD_flip_ne _ (Ne.symm (Ne.symm hkl)), getD_flip_self hk] at this
  cases y.getD k false <;> simp at this

lemma Wl_one_back {r n : ℕ} {y : List Bool} (hy : y ∈ C r n) {k : ℕ} (hk : k < n) :
    Wl r n 1 (flip y k) y = 1 := by
  have hl := (mem_C.1 hy).1
  simp only [Wl]
  rw [sum_eq_single k]
  · rw [flip_flip (by omega), if_pos (mem_C.1 hy).2, if_pos rfl]
  · intro l _ hlk
    rw [if_neg (flip_flip_ne (by omega) hlk)]
    simp
  · intro h; exact absurd (mem_range.2 hk) h

lemma flip4_ne {y : List Bool} {i j k l : ℕ} (hi : i < y.length) (hj : j < y.length)
    (hk : k < y.length) (hl : l < y.length) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    flip (flip (flip (flip y i) j) k) l ≠ y := by
  intro h
  have h1 : (flip (flip (flip (flip y i) j) k) l).getD i false = y.getD i false := by rw [h]
  have h2 : (flip (flip (flip (flip y i) j) k) l).getD j false = y.getD j false := by rw [h]
  simp only [getD_flip, length_flip, hi, hj, hk, hl] at h1 h2
  by_cases hli : l = i
  · subst hli
    simp only [if_neg hij, if_neg (Ne.symm hij), if_neg hkj, if_neg (Ne.symm hkj),
      if_neg hki, if_neg (Ne.symm hki)] at h1 h2
    cases y.getD j false <;> simp at h2
  · simp only [if_neg hli, if_neg hki, if_neg (Ne.symm hki), if_neg (Ne.symm hij),
      if_neg (Ne.symm hli)] at h1
    simp [hij] at h1

lemma Wl_two_back {r n : ℕ} {y : List Bool} (hy : y ∈ C r n) {i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) : Wl r n 2 (flip (flip y i) j) y = fl r y j + fl r y i := by
  have hl := (mem_C.1 hy).1
  have e1 : flip (flip (flip y i) j) i = flip y j := by
    rw [flip_comm (w := y) (by omega) (by omega), flip_flip (by rw [length_flip]; omega)]
  have e2 : flip (flip (flip y i) j) j = flip y i := flip_flip (by rw [length_flip]; omega)
  rw [show (2 : ℕ) = 1 + 1 from rfl, Wl]
  rw [sum_eq_add_of_mem i j (mem_range.2 hi) (mem_range.2 hj) hij]
  · rw [e1, e2, Wl_one_back hy hj, Wl_one_back hy hi]
    simp only [fl]
  · intro k hk ⟨hki, hkj⟩
    split_ifs
    · simp only [Wl]
      refine sum_eq_zero (fun l hl' => ?_)
      rw [if_neg (flip4_ne (by omega) (by omega) (by rw [mem_range] at hk; omega)
        (by rw [mem_range] at hl'; omega) hij hki hkj)]
      simp
    · rfl

lemma Wl_two_self {r n : ℕ} {y : List Bool} (hy : y ∈ C r n) : Wl r n 2 y y = dg r n y := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Wl, dg]
  refine sum_congr rfl (fun k hk => ?_)
  rw [fl]
  split_ifs
  · exact Wl_one_back hy (mem_range.1 hk)
  · rfl

lemma Wl_three_back {r n : ℕ} {y : List Bool} (hy : y ∈ C r n) {i : ℕ} (hi : i < n) :
    Wl r n 3 (flip y i) y = dg r n y +
      ∑ j ∈ (range n).erase i, fl r (flip y i) j * (fl r y j + fl r y i) := by
  have hl := (mem_C.1 hy).1
  rw [show (3 : ℕ) = 2 + 1 from rfl, Wl, ← add_sum_erase _ _ (mem_range.2 hi),
    flip_flip (by omega), if_pos (mem_C.1 hy).2, Wl_two_self hy]
  congr 1
  refine sum_congr rfl (fun j hj => ?_)
  obtain ⟨hji, hj⟩ := mem_erase.1 hj
  rw [fl]
  split_ifs
  · rw [Wl_two_back hy hi (mem_range.1 hj) (Ne.symm hji), one_mul]
  · rw [zero_mul]

lemma Wl_four {r n : ℕ} {y : List Bool} (hy : y ∈ C r n) :
    Wl r n 4 y y = ∑ i ∈ range n, fl r y i * (dg r n y +
      ∑ j ∈ (range n).erase i, fl r (flip y i) j * (fl r y j + fl r y i)) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, Wl]
  refine sum_congr rfl (fun i hi => ?_)
  by_cases h : Adm r (flip y i)
  · rw [if_pos h, Wl_three_back hy (mem_range.1 hi)]
    simp only [fl, if_pos h, one_mul]
  · rw [if_neg h]
    simp only [fl, if_neg h, zero_mul]

/-- Involution `u ↦ flip u i` on the admissible words whose `i`-flip is admissible. -/
lemma invol_sum (r n i : ℕ) (hi : i < n) (G : List Bool → ℤ) :
    ∑ u ∈ C r n, fl r u i * G (flip u i) = ∑ v ∈ C r n, fl r v i * G v := by
  simp only [fl, ite_mul, one_mul, zero_mul]
  rw [← sum_filter, ← sum_filter]
  apply sum_nbij' (fun u => flip u i) (fun u => flip u i)
  · intro u hu
    simp only [mem_filter, mem_C] at hu ⊢
    refine ⟨⟨by rw [length_flip, hu.1.1], hu.2⟩, ?_⟩
    rw [flip_flip (by omega)]; exact hu.1.2
  · intro u hu
    simp only [mem_filter, mem_C] at hu ⊢
    refine ⟨⟨by rw [length_flip, hu.1.1], hu.2⟩, ?_⟩
    rw [flip_flip (by omega)]; exact hu.1.2
  · intro u hu
    simp only [mem_filter, mem_C] at hu
    exact flip_flip (by omega)
  · intro u hu
    simp only [mem_filter, mem_C] at hu
    exact flip_flip (by omega)
  · intro u _; rfl

/-- Square indicator `[u^i][u^j][u^{ij}]`. -/
def qf (r : ℕ) (w : List Bool) (i j : ℕ) : ℤ := fl r w i * fl r w j * fl r (flip w i) j

/-- Non-closing cherry indicator `[u^i][u^j](1 − [u^{ij}])`. -/
def nf (r : ℕ) (w : List Bool) (i j : ℕ) : ℤ := fl r w i * fl r w j * (1 - fl r (flip w i) j)

/-- **Closed 4-walk decomposition.**
`Tr A⁴ = Σ_u deg u + 3 Σ_u Σ_{i≠j} [u^i][u^j][u^{ij}] + 2 Σ_u Σ_{i≠j} [u^i][u^j](1−[u^{ij}])`. -/
theorem trace_four_decomp (r n : ℕ) :
    Matrix.trace (adjMat r n ^ 4) = ∑ u ∈ C r n, dg r n u +
      3 * ∑ u ∈ C r n, ∑ i ∈ range n, ∑ j ∈ (range n).erase i, qf r u i j +
      2 * ∑ u ∈ C r n, ∑ i ∈ range n, ∑ j ∈ (range n).erase i, nf r u i j := by
  rw [trace_pow_eq_sum_Wl]
  rw [sum_congr rfl (fun y hy => Wl_four hy)]
  -- expand
  have hexp : ∀ y ∈ C r n, (∑ i ∈ range n, fl r y i * (dg r n y +
      ∑ j ∈ (range n).erase i, fl r (flip y i) j * (fl r y j + fl r y i))) =
      dg r n y * dg r n y + ∑ i ∈ range n, ∑ j ∈ (range n).erase i, qf r y i j +
      ∑ i ∈ range n, fl r y i * ∑ j ∈ (range n).erase i, fl r (flip y i) j := by
    intro y _
    rw [show dg r n y * dg r n y = ∑ i ∈ range n, fl r y i * dg r n y by
      rw [← sum_mul]; rfl, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rw [mul_add, mul_sum, mul_sum, add_assoc, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl (fun j _ => ?_)
    unfold qf
    have := fl_mul_self r y i
    linear_combination (fl r (flip y i) j) * this
  rw [sum_congr rfl hexp, sum_add_distrib, sum_add_distrib]
  -- the path term via the involution
  have hpath : ∑ y ∈ C r n, ∑ i ∈ range n, fl r y i * ∑ j ∈ (range n).erase i, fl r (flip y i) j =
      ∑ y ∈ C r n, ∑ i ∈ range n, ∑ j ∈ (range n).erase i, fl r y i * fl r y j := by
    rw [sum_comm, sum_comm (s := C r n)]
    refine sum_congr rfl (fun i hi => ?_)
    rw [invol_sum r n i (mem_range.1 hi) (fun x => ∑ j ∈ (range n).erase i, fl r x j)]
    refine sum_congr rfl (fun y _ => ?_)
    rw [mul_sum]
  rw [hpath]
  have hsq : ∀ y ∈ C r n, dg r n y * dg r n y = dg r n y +
      ∑ i ∈ range n, ∑ j ∈ (range n).erase i, fl r y i * fl r y j := by
    intro y _
    rw [dg, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl (fun i hi => ?_)
    rw [mul_sum, ← add_sum_erase _ _ hi, fl_mul_self]
  rw [sum_congr rfl hsq, sum_add_distrib]
  have hsplit : ∀ y ∈ C r n, ∑ i ∈ range n, ∑ j ∈ (range n).erase i, fl r y i * fl r y j =
      ∑ i ∈ range n, ∑ j ∈ (range n).erase i, qf r y i j +
      ∑ i ∈ range n, ∑ j ∈ (range n).erase i, nf r y i j := by
    intro y _
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun j _ => ?_)
    unfold qf nf; ring
  rw [sum_congr rfl hsplit, sum_add_distrib]
  ring

/-! ### Squares: `Σ_u [u^i][u^j][u^{ij}] = 4 · #{t : t_i = t_j = 1}` -/

/-- `0/1` value of a bit. -/
def ind (b : Bool) : ℤ := if b = true then 1 else 0

lemma ind_not (b : Bool) : ind (!b) = 1 - ind b := by cases b <;> simp [ind]

lemma fl_of_true {r : ℕ} {u : List Bool} (hu : Adm r u) {i : ℕ} (h : u.getD i false = true) :
    fl r u i = 1 := by
  rw [fl, if_pos (adm_flip_of_true hu h)]

lemma qf_comm {r : ℕ} {u : List Bool} {i j : ℕ} (hi : i < u.length) (hj : j < u.length) :
    qf r u i j = qf r u j i := by
  unfold qf fl; rw [flip_comm hi hj]; ring

lemma q_step1 (r n i j : ℕ) (hi : i < n) :
    ∑ u ∈ C r n, qf r u i j = 2 * ∑ u ∈ C r n, ind (u.getD i false) * qf r u i j := by
  have key := invol_sum r n i hi (fun x => ind (x.getD i false) * fl r (flip x i) j * fl r x j)
  have hL : ∀ u ∈ C r n, fl r u i * (ind ((flip u i).getD i false) *
      fl r (flip (flip u i) i) j * fl r (flip u i) j) =
      (1 - ind (u.getD i false)) * qf r u i j := by
    intro u hu
    have hl := (mem_C.1 hu).1
    rw [getD_flip_self (by omega), flip_flip (by omega), ind_not]
    unfold qf; ring
  rw [sum_congr rfl hL] at key
  have hR : ∀ v ∈ C r n, fl r v i * (ind (v.getD i false) * fl r (flip v i) j * fl r v j) =
      ind (v.getD i false) * qf r v i j := by
    intro v _; unfold qf; ring
  rw [sum_congr rfl hR] at key
  have : ∑ u ∈ C r n, qf r u i j = ∑ u ∈ C r n, (1 - ind (u.getD i false)) * qf r u i j +
      ∑ u ∈ C r n, ind (u.getD i false) * qf r u i j := by
    rw [← sum_add_distrib]; exact sum_congr rfl (fun u _ => by ring)
  rw [this, key]; ring

lemma q_step2 (r n i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ∑ u ∈ C r n, ind (u.getD i false) * qf r u i j =
      2 * ∑ u ∈ C r n, ind (u.getD i false) * ind (u.getD j false) := by
  have key := invol_sum r n j hj
    (fun x => ind (x.getD i false) * ind (x.getD j false) * fl r (flip x j) i * fl r x i)
  have hL : ∀ u ∈ C r n, fl r u j * (ind ((flip u j).getD i false) * ind ((flip u j).getD j false) *
      fl r (flip (flip u j) j) i * fl r (flip u j) i) =
      ind (u.getD i false) * (1 - ind (u.getD j false)) * qf r u i j := by
    intro u hu
    have hl := (mem_C.1 hu).1
    rw [getD_flip_self (by omega), getD_flip_ne _ (Ne.symm hij), flip_flip (by omega), ind_not,
      qf_comm (by omega) (by omega)]
    unfold qf; ring
  rw [sum_congr rfl hL] at key
  have hR : ∀ v ∈ C r n, fl r v j * (ind (v.getD i false) * ind (v.getD j false) *
      fl r (flip v j) i * fl r v i) = ind (v.getD i false) * ind (v.getD j false) := by
    intro v hv
    have hv' := mem_C.1 hv
    unfold ind
    by_cases h1 : v.getD i false = true <;> by_cases h2 : v.getD j false = true <;>
      simp only [h1, h2, if_true, if_false, mul_zero, zero_mul, mul_one, Bool.false_eq_true]
    rw [fl_of_true hv'.2 h2, fl_of_true hv'.2 h1, one_mul, one_mul]
    have hadm : Adm r (flip v j) := adm_flip_of_true hv'.2 h2
    rw [fl_of_true hadm (by rw [getD_flip_ne _ (Ne.symm hij)]; exact h1), mul_one]
  rw [sum_congr rfl hR] at key
  have hR2 : ∀ u ∈ C r n, ind (u.getD i false) * ind (u.getD j false) * qf r u i j =
      ind (u.getD i false) * ind (u.getD j false) := by
    intro u hu
    have hu' := mem_C.1 hu
    rw [qf_comm (by omega) (by omega)]
    unfold ind qf
    by_cases h1 : u.getD i false = true <;> by_cases h2 : u.getD j false = true <;>
      simp only [h1, h2, if_true, if_false, mul_zero, zero_mul, mul_one, Bool.false_eq_true]
    rw [fl_of_true hu'.2 h2, fl_of_true hu'.2 h1, one_mul, one_mul]
    rw [one_mul]
    exact fl_of_true (adm_flip_of_true hu'.2 h2) (by rw [getD_flip_ne _ (Ne.symm hij)]; exact h1)
  have : ∑ u ∈ C r n, ind (u.getD i false) * qf r u i j =
      ∑ u ∈ C r n, ind (u.getD i false) * (1 - ind (u.getD j false)) * qf r u i j +
      ∑ u ∈ C r n, ind (u.getD i false) * ind (u.getD j false) * qf r u i j := by
    rw [← sum_add_distrib]; exact sum_congr rfl (fun u _ => by ring)
  rw [this, key, sum_congr rfl hR2]; ring

lemma q_pair (r n i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ∑ u ∈ C r n, qf r u i j = 4 * ∑ u ∈ C r n, ind (u.getD i false) * ind (u.getD j false) := by
  rw [q_step1 r n i j hi, q_step2 r n i j hi hj hij]; ring

/-- Number of `1`s, as an integer. -/
def kap (w : List Bool) : ℤ := w.count true

lemma kap_eq (w : List Bool) : kap w = ∑ i ∈ range w.length, ind (w.getD i false) := by
  rw [kap, count_true_eq, natCast_card_filter]
  rfl

lemma sum_sq_ind (n : ℕ) (f : ℕ → Bool) :
    ∑ i ∈ range n, ∑ j ∈ (range n).erase i, ind (f i) * ind (f j) =
      (∑ i ∈ range n, ind (f i)) * (∑ i ∈ range n, ind (f i)) - ∑ i ∈ range n, ind (f i) := by
  rw [sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl (fun i hi => ?_)
  rw [mul_sum, ← add_sum_erase _ _ hi]
  have : ind (f i) * ind (f i) = ind (f i) := by unfold ind; split_ifs <;> simp
  rw [this]; ring

theorem Q_total (r n : ℕ) :
    ∑ u ∈ C r n, ∑ i ∈ range n, ∑ j ∈ (range n).erase i, qf r u i j =
      4 * ∑ u ∈ C r n, kap u * (kap u - 1) := by
  rw [sum_comm]
  rw [sum_congr rfl (fun i _ => sum_comm)]
  have h1 : ∀ i ∈ range n, ∑ j ∈ (range n).erase i, ∑ u ∈ C r n, qf r u i j =
      ∑ j ∈ (range n).erase i, 4 * ∑ u ∈ C r n, ind (u.getD i false) * ind (u.getD j false) := by
    intro i hi
    refine sum_congr rfl (fun j hj => ?_)
    obtain ⟨hji, hj⟩ := mem_erase.1 hj
    exact q_pair r n i j (mem_range.1 hi) (mem_range.1 hj) (Ne.symm hji)
  rw [sum_congr rfl h1]
  simp_rw [← mul_sum]
  congr 1
  rw [sum_congr rfl (fun i _ => sum_comm), sum_comm]
  refine sum_congr rfl (fun u hu => ?_)
  rw [sum_sq_ind n (fun i => u.getD i false), kap_eq, (mem_C.1 hu).1]
  ring

/-! ### `s₂ = Σ κ(κ−1)` -/

lemma sum_C_succ (r n : ℕ) (φ : List Bool → ℤ) :
    ∑ w ∈ C r (n + 1), φ w = ∑ w ∈ C r n, φ (false :: w) + ∑ w ∈ (C r n).filter (Z r), φ (true :: w) := by
  rw [C_succ, sum_union (C_succ_disj r n), sum_map, sum_map]
  rfl

/-- `s₂ r n = Σ_{w ∈ C r n} κ(w)(κ(w) − 1)`. -/
def s2 (r n : ℕ) : ℤ := ∑ w ∈ C r n, kap w * (kap w - 1)

lemma kap_cons (b : Bool) (w : List Bool) : kap (b :: w) = kap w + ind b := by
  cases b <;> simp [kap, ind]

lemma s2_succ (r n : ℕ) : s2 r (n + 1) = s2 r n +
    ∑ w ∈ (C r n).filter (Z r), (kap w + 1) * kap w := by
  rw [s2, sum_C_succ]
  simp only [kap_cons, ind]
  simp [s2]

theorem s2_rec (r m : ℕ) : s2 r (m + r + 1) = s2 r (m + r) + s2 r m + 2 * (e r m : ℤ) := by
  rw [s2_succ, filter_Z_of_le, sum_map]
  have hk : ∀ v : List Bool, kap (padEmb r v) = kap v := by
    intro v; simp [kap, List.count_append, List.count_replicate]
  simp only [hk]
  have he : (e r m : ℤ) = ∑ w ∈ C r m, kap w := by simp [e, kap]
  rw [he]
  unfold s2
  rw [mul_sum, add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl (fun w _ => by ring)

theorem s2_of_le (r n : ℕ) (h : n ≤ r) : s2 r n = 0 := by
  induction n with
  | zero =>
    simp only [s2, C, allL]
    rw [filter_singleton, if_pos (show Adm r [] from trivial)]
    simp [kap]
  | succ n ih =>
    rw [s2_succ, ih (by omega), filter_Z_of_lt r n (by omega), sum_singleton]
    simp [kap, List.count_replicate]

section Series4

open PowerSeries

lemma series_s2 (r : ℕ) :
    PowerSeries.mk (fun n => s2 r n) * Dser r =
      2 * X ^ (r + 1) * PowerSeries.mk (fun n => (e r n : ℤ)) := by
  ext n
  rw [coeff_mul_Dser, mul_assoc, coeff_ofNat_mul, coeff_X_pow_mul']
  simp only [coeff_mk]
  rcases Nat.lt_or_ge (r + 1) n with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + r + 1 := ⟨n - r - 1, by omega⟩
    rw [if_pos (show 1 ≤ k + r + 1 by omega), if_pos (show r + 1 ≤ k + r + 1 by omega),
      if_pos (show r + 1 ≤ k + r + 1 by omega),
      show k + r + 1 - 1 = k + r by omega, show k + r + 1 - r - 1 = k by omega,
      show k + r + 1 - (r + 1) = k by omega, s2_rec]
    ring
  · rcases Nat.lt_or_ge n (r + 1) with h' | h'
    · rw [if_neg (show ¬ (r + 1 ≤ n) by omega), if_neg (show ¬ (r + 1 ≤ n) by omega),
        s2_of_le r n (by omega)]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [if_pos (show 1 ≤ n by omega), s2_of_le r (n - 1) (by omega)]; simp
    · obtain rfl : n = r + 1 := by omega
      rw [if_pos (show 1 ≤ r + 1 by omega), if_pos le_rfl, if_pos le_rfl,
        show r + 1 - 1 = r by omega, show r + 1 - r - 1 = 0 by omega, show r + 1 - (r + 1) = 0 by omega,
        s2_of_le r r le_rfl, show r + 1 = 0 + r + 1 by omega, s2_rec, s2_of_le r (0 + r) (by omega),
        s2_of_le r 0 (by omega)]
      simp

theorem series_s2_cube (r : ℕ) :
    PowerSeries.mk (fun n => s2 r n) * Dser r ^ 3 = 2 * X ^ (r + 2) := by
  rw [pow_succ', ← mul_assoc, series_s2, mul_assoc, series_e_sq]
  ring

end Series4

/-! ### Index characterisation of admissibility -/

/-- Index form of the blockade: two `1`s are never at distance `≤ r`. -/
def AdmI (r : ℕ) (w : List Bool) : Prop :=
  ∀ s t, s < t → t ≤ s + r → w.getD s false = true → w.getD t false = false

lemma take_false_iff (r : ℕ) (l : List Bool) :
    (∀ x ∈ l.take r, x = false) ↔ ∀ t, t < r → l.getD t false = false := by
  constructor
  · intro h t ht
    rcases Nat.lt_or_ge t l.length with htl | htl
    · have hm : l[t] ∈ l.take r :=
        List.mem_iff_getElem.2 ⟨t, by simp; omega, by simp⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl]
      simpa using h _ hm
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none htl]; rfl
  · intro h x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take] at ht
    have := h t (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
    simpa using this

lemma admI_cons (r : ℕ) (b : Bool) (l : List Bool) :
    AdmI r (b :: l) ↔ (b = true → ∀ t, t < r → l.getD t false = false) ∧ AdmI r l := by
  constructor
  · intro h
    refine ⟨fun hb t ht => ?_, fun s t hst htr hs => ?_⟩
    · have := h 0 (t + 1) (by omega) (by omega) (by simpa using hb)
      simpa using this
    · have := h (s + 1) (t + 1) (by omega) (by omega) (by simpa using hs)
      simpa using this
  · rintro ⟨h1, h2⟩ s t hst htr hs
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rcases s with _ | s
    · simp only [List.getD_cons_zero] at hs
      simpa using h1 hs t' (by omega)
    · simp only [List.getD_cons_succ] at hs ⊢
      exact h2 s t' (by omega) (by omega) hs

theorem adm_iff (r : ℕ) : ∀ w : List Bool, Adm r w ↔ AdmI r w
  | [] => by
    simp only [Adm, true_iff]
    intro s t _ _ hs; simp at hs
  | b :: l => by
    rw [admI_cons, ← adm_iff r l]
    cases b
    · simp [Adm]
    · simp only [Adm, take_false_iff, forall_const]

/-- Flip criterion: `u^i` is admissible iff `u_i = 1` or the `r`-window of `i` is empty. -/
lemma fl_char {r : ℕ} {u : List Bool} (hu : Adm r u) {i : ℕ} (hi : i < u.length) :
    Adm r (flip u i) ↔ u.getD i false = true ∨
      ∀ t, t ≠ i → i ≤ t + r → t ≤ i + r → u.getD t false = false := by
  have hU := (adm_iff r u).1 hu
  rw [adm_iff]
  constructor
  · intro hF
    by_cases hb : u.getD i false = true
    · exact Or.inl hb
    · right
      intro t hti h1 h2
      rcases Nat.lt_or_gt_of_ne hti with hlt | hgt
      · by_contra hc
        have := hF t i hlt h1 (by rw [getD_flip hi, if_neg hti]; simpa using hc)
        rw [getD_flip hi, if_pos rfl] at this
        simp_all
      · have := hF i t hgt h2 (by rw [getD_flip hi, if_pos rfl]; simpa using hb)
        rwa [getD_flip hi, if_neg hti] at this
  · rintro (hb | hw)
    · exact (adm_iff r _).1 (adm_flip_of_true hu hb)
    · intro s t hst htr hs
      rw [getD_flip hi] at hs ⊢
      by_cases hsi : s = i
      · subst hsi
        rw [if_neg (by omega)]
        exact hw t (by omega) (by omega) htr
      · rw [if_neg hsi] at hs
        by_cases hti : t = i
        · subst hti
          have := hw s hsi (by omega) (by omega)
          simp_all
        · rw [if_neg hti]; exact hU s t hst htr hs

/-- Window of position `i`. -/
def Win (r i t : ℕ) : Prop := i ≤ t + r ∧ t ≤ i + r

/-- The non-closing cherry at `(i, j)`: both single flips admissible, the double flip not. -/
lemma cherry_iff {r : ℕ} {u : List Bool} (hu : Adm r u) {i j : ℕ} (hi : i < u.length)
    (hj : j < u.length) (hij : i ≠ j) :
    (Adm r (flip u i) ∧ Adm r (flip u j) ∧ ¬ Adm r (flip (flip u i) j)) ↔
      (Win r i j ∧ ∀ t, (Win r i t ∨ Win r j t) → u.getD t false = false) := by
  have hl1 : j < (flip u i).length := by rwa [length_flip]
  -- double flip of a doubly empty pair at distance > r is admissible
  have hfar : ∀ (hA : ∀ t, t ≠ i → i ≤ t + r → t ≤ i + r → u.getD t false = false)
      (hB : ∀ t, t ≠ j → j ≤ t + r → t ≤ j + r → u.getD t false = false)
      (hbi : u.getD i false = false) (hbj : u.getD j false = false),
      ¬ Win r i j → Adm r (flip (flip u i) j) := by
    intro hA hB hbi hbj hfarij
    have hv : Adm r (flip u i) := (fl_char hu hi).2 (Or.inr hA)
    refine (fl_char hv hl1).2 (Or.inr (fun t htj h1 h2 => ?_))
    rw [getD_flip hi]
    by_cases hti : t = i
    · subst hti; exact absurd ⟨by omega, by omega⟩ hfarij
    · rw [if_neg hti]; exact hB t htj h1 h2
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hbi : u.getD i false = false := by
      by_contra hc
      apply h3
      rw [flip_comm hi hj]
      exact adm_flip_of_true h2 (by rw [getD_flip_ne _ (Ne.symm hij)]; simpa using hc)
    have hbj : u.getD j false = false := by
      by_contra hc
      exact h3 (adm_flip_of_true h1 (by rw [getD_flip_ne _ hij]; simpa using hc))
    have hA := ((fl_char hu hi).1 h1).resolve_left (by rw [hbi]; decide)
    have hB := ((fl_char hu hj).1 h2).resolve_left (by rw [hbj]; decide)
    refine ⟨by_contra (fun hc => h3 (hfar hA hB hbi hbj hc)), fun t ht => ?_⟩
    rcases ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
    · by_cases hti : t = i
      · subst hti; exact hbi
      · exact hA t hti ht1 ht2
    · by_cases htj : t = j
      · subst htj; exact hbj
      · exact hB t htj ht1 ht2
  · rintro ⟨hc, hz⟩
    have hbi := hz i (Or.inl ⟨by omega, by omega⟩)
    have hbj := hz j (Or.inr ⟨by omega, by omega⟩)
    refine ⟨(fl_char hu hi).2 (Or.inr (fun t _ h1 h2 => hz t (Or.inl ⟨h1, h2⟩))),
      (fl_char hu hj).2 (Or.inr (fun t _ h1 h2 => hz t (Or.inr ⟨h1, h2⟩))), fun hadm => ?_⟩
    have hI := (adm_iff r _).1 hadm
    have gi : (flip (flip u i) j).getD i false = true := by
      rw [getD_flip_ne _ (Ne.symm hij), getD_flip_self hi, hbi]; rfl
    have gj : (flip (flip u i) j).getD j false = true := by
      rw [getD_flip_self hl1, getD_flip_ne _ hij, hbj]; rfl
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · have := hI i j hlt hc.2 gi; simp_all
    · have := hI j i hgt hc.1 gj; simp_all

lemma nf_eq (r : ℕ) (u : List Bool) (i j : ℕ) :
    nf r u i j = if (Adm r (flip u i) ∧ Adm r (flip u j) ∧ ¬ Adm r (flip (flip u i) j))
      then 1 else 0 := by
  unfold nf fl
  by_cases h1 : Adm r (flip u i) <;> by_cases h2 : Adm r (flip u j) <;>
    by_cases h3 : Adm r (flip (flip u i) j) <;> simp [h1, h2, h3]

/-! ### Words with a prescribed block of zeros -/

lemma mem_take_zeros {k m : ℕ} {y : List Bool} (hm : m ≤ k ∨ y = []) {z : Bool}
    (hz : z ∈ (List.replicate k false ++ y).take m) : z = false := by
  rw [List.take_append] at hz
  rcases List.mem_append.1 hz with h | h
  · rw [List.take_replicate] at h; exact List.eq_of_mem_replicate h
  · rcases hm with hm | rfl
    · rw [List.length_replicate, show m - k = 0 by omega, List.take_zero] at h; simp at h
    · simp at h

lemma adm_block (r k : ℕ) (y : List Bool) :
    ∀ x : List Bool, (r ≤ k ∨ x = [] ∨ y = []) →
      (Adm r (x ++ (List.replicate k false ++ y)) ↔ Adm r x ∧ Adm r y)
  | [], _ => by simp [adm_replicate_append, Adm]
  | b :: x, h => by
    have h' : r ≤ k ∨ y = [] := by
      rcases h with h | h | h
      · exact Or.inl h
      · simp at h
      · exact Or.inr h
    have ih := adm_block r k y x (by rcases h' with h' | h' <;> simp [h'])
    cases b
    · simpa [Adm] using ih
    · simp only [List.cons_append, Adm]
      rw [ih]
      have : (∀ z ∈ (x ++ (List.replicate k false ++ y)).take r, z = false) ↔
          (∀ z ∈ x.take r, z = false) := by
        rw [List.take_append]
        constructor
        · intro hz z hzm; exact hz z (List.mem_append_left _ hzm)
        · intro hz z hzm
          rcases List.mem_append.1 hzm with hzm | hzm
          · exact hz z hzm
          · have hm : r - x.length ≤ k ∨ y = [] := by
              rcases h' with h' | h'
              · left; omega
              · right; exact h'
            exact mem_take_zeros hm hzm
      rw [this]; tauto

/-- **Zero-block count.**  Admissible words of length `n` vanishing on `[lo, hi)` factor as
`x ++ 0^{hi−lo} ++ y`, provided the block separates (`r ≤ hi − lo`) or touches an end. -/
theorem card_zero_block (r n lo hi : ℕ) (h1 : lo ≤ hi) (h2 : hi ≤ n)
    (hsep : r ≤ hi - lo ∨ lo = 0 ∨ hi = n) :
    ((C r n).filter (fun u => ∀ t ∈ Ico lo hi, u.getD t false = false)).card =
      a r lo * a r (n - hi) := by
  rw [a, a, ← card_product]
  symm
  apply card_bij (fun p _ => p.1 ++ (List.replicate (hi - lo) false ++ p.2))
  · intro p hp
    rw [mem_product, mem_C, mem_C] at hp
    obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := hp
    have hs : r ≤ hi - lo ∨ p.1 = [] ∨ p.2 = [] := by
      rcases hsep with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
      · exact Or.inr (Or.inr (List.eq_nil_of_length_eq_zero (by omega)))
    rw [mem_filter, mem_C]
    refine ⟨⟨by simp [hx1, hy1]; omega, (adm_block r (hi - lo) p.2 p.1 hs).2 ⟨hx2, hy2⟩⟩, ?_⟩
    intro t ht
    rw [mem_Ico] at ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getElem?_append_left (by simp; omega), List.getElem?_replicate_of_lt (by omega)]
    rfl
  · intro p hp q hq h
    rw [mem_product, mem_C, mem_C] at hp hq
    obtain ⟨h1', h2'⟩ := List.append_inj h (by rw [hp.1.1, hq.1.1])
    exact Prod.ext h1' (List.append_cancel_left h2')
  · intro u hu
    rw [mem_filter, mem_C] at hu
    obtain ⟨⟨hl, ha⟩, hz⟩ := hu
    have hdec : u = u.take lo ++ (List.replicate (hi - lo) false ++ u.drop hi) := by
      apply ext_getD (by simp [hl]; omega)
      intro t
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rcases Nat.lt_or_ge t lo with h | h
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt h]
      · rw [List.getElem?_append_right (by simp; omega)]
        simp only [List.length_take, show min lo u.length = lo by omega]
        rcases Nat.lt_or_ge t hi with h' | h'
        · rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate_of_lt (by omega)]
          have := hz t (mem_Ico.2 ⟨h, h'⟩)
          rw [List.getD_eq_getElem?_getD] at this
          rw [this]; rfl
        · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop]
          simp only [List.length_replicate]
          congr 2
          omega
    have hs : r ≤ hi - lo ∨ u.take lo = [] ∨ u.drop hi = [] := by
      rcases hsep with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.eq_nil_of_length_eq_zero (by simp; omega)))
      · exact Or.inr (Or.inr (List.eq_nil_of_length_eq_zero (by simp; omega)))
    rw [hdec] at ha
    have hab := (adm_block r (hi - lo) (u.drop hi) (u.take lo) hs).1 ha
    refine ⟨(u.take lo, u.drop hi), ?_, hdec.symm⟩
    rw [mem_product, mem_C, mem_C]
    exact ⟨⟨by simp; omega, hab.1⟩, by simp; omega, hab.2⟩

/-- **Cherry count at a pair** `i ≠ j`. -/
theorem nf_pair (r n i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ∑ u ∈ C r n, nf r u i j =
      if j ≤ i + r ∧ i ≤ j + r then
        (a r (min i j - r) : ℤ) * a r (n - 1 - max i j - r) else 0 := by
  simp only [nf_eq]
  rw [sum_boole]
  split_ifs with hc
  · obtain ⟨lo, hlo⟩ : ∃ lo, lo = min i j - r := ⟨_, rfl⟩
    obtain ⟨hi', hhi⟩ : ∃ hi', hi' = min n (max i j + r + 1) := ⟨_, rfl⟩
    have hcongr : (C r n).filter (fun u => Adm r (flip u i) ∧ Adm r (flip u j) ∧
        ¬ Adm r (flip (flip u i) j)) = (C r n).filter (fun u =>
          ∀ t ∈ Ico lo hi', u.getD t false = false) := by
      apply filter_congr
      intro u hu
      have hu' := mem_C.1 hu
      rw [cherry_iff hu'.2 (by omega) (by omega) hij]
      constructor
      · rintro ⟨-, hz⟩ t ht
        rw [mem_Ico] at ht
        apply hz
        unfold Win
        omega
      · intro hz
        refine ⟨⟨by omega, by omega⟩, fun t ht => ?_⟩
        rcases Nat.lt_or_ge t n with htn | htn
        · apply hz
          rw [mem_Ico]
          unfold Win at ht
          omega
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [hcongr, card_zero_block r n lo hi' (by omega) (by omega) (by omega), hlo,
      show n - hi' = n - 1 - max i j - r by omega]
    push_cast; rfl
  · rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
    intro u hu h
    have := (cherry_iff (mem_C.1 hu).2 (by rw [(mem_C.1 hu).1]; omega)
      (by rw [(mem_C.1 hu).1]; omega) hij).1 h
    exact hc ⟨this.1.2, this.1.1⟩

/-! ### Totals -/

/-- Summand of the cherry total. -/
def gN (r n i j : ℕ) : ℤ :=
  if j ≤ i + r ∧ i ≤ j + r then (a r (min i j - r) : ℤ) * a r (n - 1 - max i j - r) else 0

/-- The cherry total as an explicit double sum. -/
def hN (r n : ℕ) : ℤ := ∑ i ∈ range n, ∑ j ∈ (range n).erase i, gN r n i j

theorem N_total (r n : ℕ) :
    ∑ u ∈ C r n, ∑ i ∈ range n, ∑ j ∈ (range n).erase i, nf r u i j = hN r n := by
  rw [sum_comm, hN]
  refine sum_congr rfl (fun i hi => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun j hj => ?_)
  obtain ⟨hji, hj⟩ := mem_erase.1 hj
  exact nf_pair r n i j (mem_range.1 hi) (mem_range.1 hj) (Ne.symm hji)

theorem sum_dg (r n : ℕ) : ∑ u ∈ C r n, dg r n u = 2 * (e r n : ℤ) := by
  rw [← trace_sq_eq, trace_sq_eq_sum_deg]
  refine sum_congr rfl (fun u _ => ?_)
  rw [dg, natCast_card_filter]
  rfl

/-- `Tr A⁴ = 2e + 12 s₂ + 2 hN`. -/
theorem trace_four_eq (r n : ℕ) :
    Matrix.trace (adjMat r n ^ 4) = 2 * (e r n : ℤ) + 12 * s2 r n + 2 * hN r n := by
  rw [trace_four_decomp, sum_dg, Q_total, N_total, s2]
  ring

/-! ### The cherry series -/

lemma hN_eq (r n : ℕ) : hN r n = 2 * ∑ δ ∈ range r, ∑ i ∈ range (n - δ - 1),
    (a r (i - r) : ℤ) * a r (n - δ - 2 - i - r) := by
  have hsym : ∀ i j, gN r n i j = gN r n j i := by
    intro i j; simp only [gN, min_comm, max_comm, and_comm]
  have h1 : hN r n = ∑ i ∈ range n, ∑ j ∈ range n,
      ((if i < j then gN r n i j else 0) + (if j < i then gN r n i j else 0)) := by
    rw [hN]
    refine sum_congr rfl (fun i hi => ?_)
    rw [← add_sum_erase (range n) (fun j => (if i < j then gN r n i j else 0) +
      (if j < i then gN r n i j else 0)) hi]
    simp only [lt_irrefl, if_false, add_zero, zero_add]
    refine sum_congr rfl (fun j hj => ?_)
    obtain ⟨hji, -⟩ := mem_erase.1 hj
    rcases Nat.lt_or_gt_of_ne hji with h | h
    · rw [if_neg (show ¬ i < j by omega), if_pos h, zero_add]
    · rw [if_pos (show i < j by omega), if_neg (show ¬ j < i by omega), add_zero]
  have h2 : ∑ i ∈ range n, ∑ j ∈ range n, (if j < i then gN r n i j else 0) =
      ∑ i ∈ range n, ∑ j ∈ range n, (if i < j then gN r n i j else 0) := by
    rw [sum_comm]
    refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
    rw [hsym]
  have h3 : ∀ i ∈ range n, ∑ j ∈ range n, (if i < j then gN r n i j else 0) =
      ∑ δ ∈ range r, if i + δ + 1 < n then
        (a r (i - r) : ℤ) * a r (n - δ - 2 - i - r) else 0 := by
    intro i _
    have h3a : ∑ j ∈ range n, (if i < j then gN r n i j else 0) =
        ∑ j ∈ range n, (if i < j ∧ j ≤ i + r then
          (a r (i - r) : ℤ) * a r (n - 1 - j - r) else 0) := by
      refine sum_congr rfl (fun j _ => ?_)
      unfold gN
      by_cases hij : i < j
      · by_cases hc : j ≤ i + r
        · rw [if_pos hij, if_pos ⟨hc, by omega⟩, if_pos ⟨hij, hc⟩, min_eq_left (by omega),
            max_eq_right (by omega)]
        · rw [if_pos hij, if_neg (by omega), if_neg (by omega)]
      · rw [if_neg hij, if_neg (by omega)]
    rw [h3a, ← sum_filter, ← sum_filter]
    apply sum_nbij' (fun j => j - i - 1) (fun δ => i + δ + 1)
    · intro j hj
      simp only [mem_filter, mem_range] at hj ⊢
      omega
    · intro δ hδ
      simp only [mem_filter, mem_range] at hδ ⊢
      omega
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      omega
    · intro δ hδ
      simp only [mem_filter, mem_range] at hδ
      omega
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      rw [show n - (j - i - 1) - 2 - i - r = n - 1 - j - r by omega]
  rw [h1, sum_congr rfl (fun i _ => sum_add_distrib), sum_add_distrib, h2, ← two_mul,
    sum_congr rfl h3, sum_comm]
  congr 1
  refine sum_congr rfl (fun δ _ => ?_)
  rw [← sum_filter]
  apply sum_congr
  · ext i; simp only [mem_filter, mem_range]; omega
  · intro i _; rfl

section Final

open PowerSeries

/-- `F = ∑ a_{p−r} z^p = 1/D_r` (boundary factor). -/
noncomputable def Fser (r : ℕ) : PowerSeries ℤ := PowerSeries.mk (fun p => (a r (p - r) : ℤ))

lemma Fser_eq (r : ℕ) :
    Fser r = ∑ g ∈ range r, (X : PowerSeries ℤ) ^ g + X ^ r * PowerSeries.mk (fun n => (a r n : ℤ)) := by
  ext n
  rw [Fser, map_add, coeff_geom, coeff_X_pow_mul', coeff_mk, coeff_mk]
  rcases Nat.lt_or_ge n r with h | h
  · rw [if_pos h, if_neg (by omega), show n - r = 0 by omega, a_zero]; simp
  · rw [if_neg (by omega), if_pos h, zero_add]

lemma Fser_mul (r : ℕ) : Fser r * Dser r = 1 := by
  rw [Fser_eq, add_mul, mul_assoc, series_a]
  have := ident_a (X : PowerSeries ℤ) r
  rw [Dser]
  linear_combination this

lemma coeff_cherry (r δ n : ℕ) :
    coeff n ((X : PowerSeries ℤ) ^ (δ + 2) * (Fser r * Fser r)) =
      ∑ i ∈ range (n - δ - 1), (a r (i - r) : ℤ) * a r (n - δ - 2 - i - r) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun p q => coeff p (Fser r) * coeff q (Fser r))]
    simp only [Fser, coeff_mk]
    rw [show (n - (δ + 2)).succ = n - δ - 1 by omega]
    refine sum_congr rfl (fun k _ => ?_)
    rw [show n - (δ + 2) - k - r = n - δ - 2 - k - r by omega]
  · rw [show n - δ - 1 = 0 by omega]; simp

lemma series_hN (r : ℕ) : PowerSeries.mk (fun n => hN r n) =
    2 * ∑ δ ∈ range r, (X : PowerSeries ℤ) ^ (δ + 2) * (Fser r * Fser r) := by
  ext n
  rw [coeff_mk, hN_eq, coeff_ofNat_mul, map_sum]
  simp only [coeff_cherry]

theorem series_hN_sq (r : ℕ) : PowerSeries.mk (fun n => hN r n) * Dser r ^ 2 =
    2 * X ^ 2 * ∑ g ∈ range r, (X : PowerSeries ℤ) ^ g := by
  have h : ∀ δ : ℕ, (X : PowerSeries ℤ) ^ (δ + 2) * (Fser r * Fser r) * Dser r ^ 2 =
      X ^ 2 * X ^ δ := by
    intro δ
    have h' : (X : PowerSeries ℤ) ^ (δ + 2) * (Fser r * Fser r) * Dser r ^ 2 =
        X ^ (δ + 2) * (Fser r * Dser r) ^ 2 := by ring
    rw [h', Fser_mul, one_pow, mul_one, pow_add]
    ring
  rw [series_hN, mul_assoc, sum_mul, sum_congr rfl (fun δ _ => h δ), ← mul_sum, mul_assoc]

/-- **Fourth moment for every range `r`** (Conj4 of `Moments.lean`):
`(∑ₙ Tr A_{n,r}⁴ zⁿ) · D_r³ = 2z·D_r + 4z²(1 + … + z^{r−1})·D_r + 24 z^{r+2}`. -/
theorem fourth_moment (r : ℕ) : Conj4 r := by
  unfold Conj4
  have hT : PowerSeries.mk (fun n => Mk 4 r n) =
      2 * PowerSeries.mk (fun n => (e r n : ℤ)) + 12 * PowerSeries.mk (fun n => s2 r n) +
        2 * PowerSeries.mk (fun n => hN r n) := by
    ext n
    rw [coeff_mk, Mk, trace_four_eq, map_add, map_add, coeff_ofNat_mul, coeff_ofNat_mul,
      coeff_ofNat_mul, coeff_mk, coeff_mk, coeff_mk]
  have he := series_e_sq r
  have hs := series_s2_cube r
  have hn := series_hN_sq r
  rw [Dser] at he hs hn
  rw [hT]
  linear_combination (2 * (1 - X - X ^ (r + 1))) * he + 12 * hs + (2 * (1 - X - X ^ (r + 1))) * hn

/-- Coefficient form of the trace formula: `Tr A_{n,r}⁴ = 2eₙ + 12 s₂(n) + 2 hN(n)`. -/
theorem Mk_four_eq (r n : ℕ) : Mk 4 r n = 2 * (e r n : ℤ) + 12 * s2 r n + 2 * hN r n :=
  trace_four_eq r n

end Final

end APEX.Blockade

