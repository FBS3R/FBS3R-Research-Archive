import OpenProblems.Prelude
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort

/-!
# Small classical Ramsey numbers: `R(3,3)=6`, `R(3,4)=9`, `R(3,5)=14`, `R(4,4)=18`

Source: `formal-conjectures`, `Wikipedia/RamseyNumbers.lean`, theorems
`ramsey_number_three_three`, `ramsey_number_three_four`, `ramsey_number_three_five`,
`ramsey_number_four_four` (category `research solved`, proofs `sorry`). Mathlib has no Ramsey
numbers. We use the catalogue's own predicate `IsGraphRamsey` (copied verbatim) and prove
`sInf {n | IsGraphRamsey n k l} = R` — in the catalogue this is `SimpleGraph.classicalRamsey k l`
by its API lemma `classicalRamsey_eq_sInf`.

* upper bounds: the Erdős–Szekeres recursion `R(k+1,l+1) ≤ R(k,l+1) + R(k+1,l)`, plus the
  Greenwood–Gleason parity argument for `R(3,4) ≤ 9`;
* lower bounds: explicit circulant graphs (the 5-cycle, the circulants `C₈(1,4)`, `C₁₃(1,5)`
  and the Paley graph on 17 vertices) checked by kernel computation.
-/

namespace OpenProblems.Ramsey

open Finset SimpleGraph

/-- Verbatim from formal-conjectures. -/
def IsGraphRamsey (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ (Gᶜ).CliqueFree l)

/-- Monotonicity in the number of vertices (re-proved here, as in the catalogue). -/
theorem IsGraphRamsey.mono {n m k l : ℕ} (h : IsGraphRamsey n k l) (hnm : n ≤ m) :
    IsGraphRamsey m k l := by
  intro G ⟨hG, hGc⟩
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  let H : SimpleGraph (Fin n) := G.comap f
  have emb : H ↪g G := Embedding.comap f G
  have embc : Hᶜ ↪g Gᶜ := (Embedding.complEquiv (G := H) (H := G)).toFun emb
  exact h H ⟨hG.comap emb.isContained, hGc.comap embc.isContained⟩

/-! ### A finset-relative Ramsey property, convenient for induction -/

/-- Every `s` with at least `n` vertices contains a `k`-clique or an independent `l`-set. -/
def Ram (k l n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (s : Finset V), n ≤ #s →
    (∃ t ⊆ s, G.IsNClique k t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique l t)

theorem Ram.symm {k l n : ℕ} (h : Ram k l n) : Ram l k n := by
  intro V _ _ G s hs
  rcases h V Gᶜ s hs with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
  · exact Or.inr ⟨t, ht, h⟩
  · exact Or.inl ⟨t, ht, by simpa using h⟩

theorem Ram.two (l : ℕ) : Ram 2 l l := by
  intro V _ _ G s hs
  by_cases hadj : ∃ x ∈ s, ∃ y ∈ s, G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hadj
    refine Or.inl ⟨{x, y}, by simp [insert_subset_iff, hx, hy], ?_⟩
    rw [isNClique_iff, coe_pair, isClique_iff, Set.pairwise_pair]
    exact ⟨fun _ => ⟨hxy, hxy.symm⟩, card_pair hxy.ne⟩
  · push_neg at hadj
    obtain ⟨t, hts, htc⟩ := exists_subset_card_eq hs
    refine Or.inr ⟨t, hts, ⟨?_, htc⟩⟩
    intro x hx y hy hne
    exact (compl_adj G x y).2 ⟨hne, hadj x (hts hx) y (hts hy)⟩

/-- **Erdős–Szekeres recursion.** -/
theorem Ram.step {k l a b : ℕ} (ha : Ram k (l + 1) a) (hb : Ram (k + 1) l b) (hab : 0 < a + b) :
    Ram (k + 1) (l + 1) (a + b) := by
  intro V _ _ G s hs
  classical
  obtain ⟨v, hv⟩ : s.Nonempty := card_pos.1 (by omega)
  set N := (s.erase v).filter (G.Adj v)
  set M := (s.erase v).filter (fun w => ¬ G.Adj v w)
  have hcard : #N + #M = #s - 1 := by
    rw [card_filter_add_card_filter_not, card_erase_of_mem hv]
  have hNs : N ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
  have hMs : M ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
  rcases (show a ≤ #N ∨ b ≤ #M by omega) with hN | hM
  · rcases ha V G N hN with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
    · refine Or.inl ⟨insert v t, insert_subset hv (ht.trans hNs), hc.insert fun w hw => ?_⟩
      exact (mem_filter.1 (ht hw)).2
    · exact Or.inr ⟨t, ht.trans hNs, hc⟩
  · rcases hb V G M hM with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
    · exact Or.inl ⟨t, ht.trans hMs, hc⟩
    · refine Or.inr ⟨insert v t, insert_subset hv (ht.trans hMs), hc.insert fun w hw => ?_⟩
      have hw' := mem_filter.1 (ht hw)
      exact (compl_adj G v w).2 ⟨(ne_of_mem_erase hw'.1).symm, hw'.2⟩

theorem Ram.isGraphRamsey {k l n : ℕ} (h : Ram k l n) : IsGraphRamsey n k l := by
  intro G ⟨hG, hGc⟩
  classical
  rcases h (Fin n) G univ (by simp) with ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  · exact hG t ht
  · exact hGc t ht

theorem ram_3_3 : Ram 3 3 6 := Ram.step (Ram.two 3) (Ram.two 3).symm (by norm_num)

/-- **Greenwood–Gleason**: every graph on 9 vertices has a triangle or an independent 4-set. -/
theorem isGraphRamsey_9_3_4 : IsGraphRamsey 9 3 4 := by
  classical
  intro G ⟨hG, hGc⟩
  have hdeg : ∀ v, G.degree v = 3 := by
    intro v
    apply le_antisymm
    · -- the neighbourhood is independent, hence has at most 3 vertices
      by_contra hlt
      push_neg at hlt
      rcases Ram.two 4 (Fin 9) G (G.neighborFinset v) (by rw [card_neighborFinset_eq_degree]; omega)
        with ⟨t, ht, hc⟩ | ⟨t, -, hc⟩
      · refine hG (insert v t) (hc.insert fun w hw => ?_)
        exact (mem_neighborFinset G v w).1 (ht hw)
      · exact hGc t hc
    · -- the non-neighbourhood has no triangle and no independent 3-set, so at most 5 vertices
      by_contra hlt
      push_neg at hlt
      set M := (univ.erase v).filter (fun w => ¬ G.Adj v w)
      have hcard : #(G.neighborFinset v) + #M = 8 := by
        have : (univ.erase v).filter (G.Adj v) = G.neighborFinset v := by
          ext w; simp only [mem_filter, mem_erase, mem_univ, and_true, mem_neighborFinset]
          exact ⟨fun h => h.2, fun h => ⟨h.ne.symm, h⟩⟩
        rw [← this, card_filter_add_card_filter_not, card_erase_of_mem (mem_univ _)]
        simp
      rw [card_neighborFinset_eq_degree] at hcard
      rcases ram_3_3 (Fin 9) G M (by omega) with ⟨t, -, hc⟩ | ⟨t, ht, hc⟩
      · exact hG t hc
      · refine hGc (insert v t) (hc.insert fun w hw => ?_)
        have hw' := mem_filter.1 (ht hw)
        exact (compl_adj G v w).2 ⟨(ne_of_mem_erase hw'.1).symm, hw'.2⟩
  have := G.sum_degrees_eq_twice_card_edges
  simp only [hdeg, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

/-- `Ram 3 4 9`, obtained from the Fin-9 statement by restricting to a subset. -/
theorem ram_3_4 : Ram 3 4 9 := by
  intro V _ _ G s hs
  classical
  obtain ⟨u, hus, huc⟩ := exists_subset_card_eq hs
  let e : Fin 9 ≃ u := (u.equivFinOfCardEq huc).symm
  let f : Fin 9 ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hf : ∀ i, f i ∈ u := fun i => (e i).2
  by_contra hno
  push_neg at hno
  refine isGraphRamsey_9_3_4 (G.comap f) ⟨fun t ht => ?_, fun t ht => ?_⟩
  · refine (hno.1 (t.map f) (fun x hx => ?_)) ?_
    · obtain ⟨i, -, rfl⟩ := mem_map.1 hx; exact hus (hf i)
    · rw [isNClique_iff] at ht ⊢
      refine ⟨?_, by simp [ht.2]⟩
      intro x hx y hy hne
      obtain ⟨i, hi, rfl⟩ := mem_map.1 hx
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hy
      have := ht.1 hi hj (fun h => hne (h ▸ rfl))
      simpa using this
  · refine (hno.2 (t.map f) (fun x hx => ?_)) ?_
    · obtain ⟨i, -, rfl⟩ := mem_map.1 hx; exact hus (hf i)
    · rw [isNClique_iff] at ht ⊢
      refine ⟨?_, by simp [ht.2]⟩
      intro x hx y hy hne
      obtain ⟨i, hi, rfl⟩ := mem_map.1 hx
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hy
      have := ht.1 hi hj (fun h => hne (h ▸ rfl))
      simpa [compl_adj] using this

theorem ram_3_5 : Ram 3 5 14 := Ram.step (Ram.two 5) ram_3_4 (by norm_num)

theorem ram_4_4 : Ram 4 4 18 := Ram.step ram_3_4 ram_3_4.symm (by norm_num)

/-! ### Lower-bound graphs -/

/-- Adjacency of the circulant graph with connection set `S`, as a Boolean function on `ℕ`. -/
def cAdj (n : ℕ) (S : List ℕ) (i j : ℕ) : Bool :=
  i != j && (S.contains ((i + n - j) % n) || S.contains ((j + n - i) % n))

theorem cAdj_comm (n : ℕ) (S : List ℕ) (i j : ℕ) : cAdj n S i j = cAdj n S j i := by
  unfold cAdj; rw [bne_comm, Bool.or_comm]

/-- The circulant graph on `Fin n` with connection set `S` (a list of residues). -/
def circulant (n : ℕ) (S : List ℕ) : SimpleGraph (Fin n) where
  Adj i j := cAdj n S i.val j.val = true
  symm := ⟨fun i j h => by rw [cAdj_comm]; exact h⟩
  loopless := ⟨fun i h => by simp [cAdj] at h⟩

/-- Adjacency of the complement, as a Boolean function. -/
def cNonAdj (n : ℕ) (S : List ℕ) (i j : ℕ) : Bool := i != j && !cAdj n S i j

theorem circulant_adj {n : ℕ} {S : List ℕ} (i j : Fin n) :
    (circulant n S).Adj i j → cAdj n S i j = true := id

theorem circulant_compl_adj {n : ℕ} {S : List ℕ} (i j : Fin n) :
    (circulant n S)ᶜ.Adj i j → cNonAdj n S i j = true := by
  intro h
  rw [compl_adj] at h
  have hne : (i : ℕ) ≠ j := Fin.val_ne_of_ne h.1
  simp only [cNonAdj, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
  exact ⟨hne, by simpa [circulant] using h.2⟩

/-- From a `k`-clique, a strictly increasing enumeration of pairwise adjacent vertices. -/
theorem clique_emb {n k : ℕ} {G : SimpleGraph (Fin n)} {t : Finset (Fin n)}
    (ht : G.IsNClique k t) :
    ∃ e : Fin k → Fin n, StrictMono e ∧ ∀ i j, i ≠ j → G.Adj (e i) (e j) :=
  ⟨fun i => t.orderEmbOfFin ht.2 i, (t.orderEmbOfFin ht.2).strictMono, fun i j hij =>
    ht.1 (t.orderEmbOfFin_mem ht.2 i) (t.orderEmbOfFin_mem ht.2 j)
      (fun h => hij ((t.orderEmbOfFin ht.2).injective h))⟩

/-- Boolean check: no `3` indices `a > b > ⋯` below `n` are pairwise `A`-related. -/
def free3 (A : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  (List.range n).all fun a => (List.range a).all fun b => (List.range b).all fun c => !(A a b && A a c && A b c)

theorem cliqueFree_of_free3 {n : ℕ} (G : SimpleGraph (Fin n)) (A : ℕ → ℕ → Bool)
    (hA : ∀ i j : Fin n, G.Adj i j → A i j = true) (h : free3 A n = true) : G.CliqueFree 3 := by
  intro t ht
  obtain ⟨e, he, hadj⟩ := clique_emb ht
  simp only [free3, List.all_eq_true, List.mem_range] at h
  have := h (e 2) (e 2).isLt (e 1) (he (by decide)) (e 0) (he (by decide))
  simp [hA _ _ (hadj 2 1 (by decide)), hA _ _ (hadj 2 0 (by decide)), hA _ _ (hadj 1 0 (by decide))] at this

/-- Boolean check: no `4` indices `a > b > ⋯` below `n` are pairwise `A`-related. -/
def free4 (A : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  (List.range n).all fun a => (List.range a).all fun b => (List.range b).all fun c => (List.range c).all fun d => !(A a b && A a c && A a d && A b c && A b d && A c d)

theorem cliqueFree_of_free4 {n : ℕ} (G : SimpleGraph (Fin n)) (A : ℕ → ℕ → Bool)
    (hA : ∀ i j : Fin n, G.Adj i j → A i j = true) (h : free4 A n = true) : G.CliqueFree 4 := by
  intro t ht
  obtain ⟨e, he, hadj⟩ := clique_emb ht
  simp only [free4, List.all_eq_true, List.mem_range] at h
  have := h (e 3) (e 3).isLt (e 2) (he (by decide)) (e 1) (he (by decide)) (e 0) (he (by decide))
  simp [hA _ _ (hadj 3 2 (by decide)), hA _ _ (hadj 3 1 (by decide)), hA _ _ (hadj 3 0 (by decide)), hA _ _ (hadj 2 1 (by decide)), hA _ _ (hadj 2 0 (by decide)), hA _ _ (hadj 1 0 (by decide))] at this

/-- Boolean check: no `5` indices `a > b > ⋯` below `n` are pairwise `A`-related. -/
def free5 (A : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  (List.range n).all fun a => (List.range a).all fun b => (List.range b).all fun c => (List.range c).all fun d => (List.range d).all fun e => !(A a b && A a c && A a d && A a e && A b c && A b d && A b e && A c d && A c e && A d e)

theorem cliqueFree_of_free5 {n : ℕ} (G : SimpleGraph (Fin n)) (A : ℕ → ℕ → Bool)
    (hA : ∀ i j : Fin n, G.Adj i j → A i j = true) (h : free5 A n = true) : G.CliqueFree 5 := by
  intro t ht
  obtain ⟨e, he, hadj⟩ := clique_emb ht
  simp only [free5, List.all_eq_true, List.mem_range] at h
  have := h (e 4) (e 4).isLt (e 3) (he (by decide)) (e 2) (he (by decide)) (e 1) (he (by decide)) (e 0) (he (by decide))
  simp [hA _ _ (hadj 4 3 (by decide)), hA _ _ (hadj 4 2 (by decide)), hA _ _ (hadj 4 1 (by decide)), hA _ _ (hadj 4 0 (by decide)), hA _ _ (hadj 3 2 (by decide)), hA _ _ (hadj 3 1 (by decide)), hA _ _ (hadj 3 0 (by decide)), hA _ _ (hadj 2 1 (by decide)), hA _ _ (hadj 2 0 (by decide)), hA _ _ (hadj 1 0 (by decide))] at this

theorem not_isGraphRamsey_5_3_3 : ¬ IsGraphRamsey 5 3 3 := fun h =>
  h (circulant 5 [1, 4]) ⟨cliqueFree_of_free3 _ _ circulant_adj (by decide +kernel),
    cliqueFree_of_free3 _ _ circulant_compl_adj (by decide +kernel)⟩

theorem not_isGraphRamsey_8_3_4 : ¬ IsGraphRamsey 8 3 4 := fun h =>
  h (circulant 8 [1, 4, 7]) ⟨cliqueFree_of_free3 _ _ circulant_adj (by decide +kernel),
    cliqueFree_of_free4 _ _ circulant_compl_adj (by decide +kernel)⟩

theorem not_isGraphRamsey_13_3_5 : ¬ IsGraphRamsey 13 3 5 := fun h =>
  h (circulant 13 [1, 5, 8, 12]) ⟨cliqueFree_of_free3 _ _ circulant_adj (by decide +kernel),
    cliqueFree_of_free5 _ _ circulant_compl_adj (by decide +kernel)⟩

theorem not_isGraphRamsey_17_4_4 : ¬ IsGraphRamsey 17 4 4 := fun h =>
  h (circulant 17 [1, 2, 4, 8, 9, 13, 15, 16]) ⟨cliqueFree_of_free4 _ _ circulant_adj
    (by decide +kernel), cliqueFree_of_free4 _ _ circulant_compl_adj (by decide +kernel)⟩

theorem sInf_eq {k l R : ℕ} (hR : IsGraphRamsey R k l) (hR' : ¬ IsGraphRamsey (R - 1) k l)
    (hpos : 0 < R) : sInf {n | IsGraphRamsey n k l} = R := by
  apply le_antisymm (Nat.sInf_le hR)
  apply le_csInf ⟨R, hR⟩
  intro n hn
  by_contra hlt
  exact hR' (hn.mono (by omega))

/-- `R(3,3) = 6`. -/
theorem ramsey_three_three : sInf {n | IsGraphRamsey n 3 3} = 6 :=
  sInf_eq ram_3_3.isGraphRamsey not_isGraphRamsey_5_3_3 (by norm_num)

/-- `R(3,4) = 9`. -/
theorem ramsey_three_four : sInf {n | IsGraphRamsey n 3 4} = 9 :=
  sInf_eq isGraphRamsey_9_3_4 not_isGraphRamsey_8_3_4 (by norm_num)

/-- `R(3,5) = 14`. -/
theorem ramsey_three_five : sInf {n | IsGraphRamsey n 3 5} = 14 :=
  sInf_eq ram_3_5.isGraphRamsey not_isGraphRamsey_13_3_5 (by norm_num)

/-- `R(4,4) = 18`. -/
theorem ramsey_four_four : sInf {n | IsGraphRamsey n 4 4} = 18 :=
  sInf_eq ram_4_4.isGraphRamsey not_isGraphRamsey_17_4_4 (by norm_num)

end OpenProblems.Ramsey
