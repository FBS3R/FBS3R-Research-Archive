import OpenProblems.Prelude
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort

/-!
# Written on the Wall II, Conjecture 91 is false

Source: `formal-conjectures`, `WrittenOnTheWallII/GraphConjecture91.lean`, theorem
`conjecture91` (category `research solved`, proof `sorry`).

The conjecture: for every connected graph `G`, `b(G) ≤ 1 + f(G)·⌈l(G)⌉/2`, where `b` is the
largest induced bipartite subgraph, `f` the largest induced forest and `l` the average
independence number of neighbourhoods. Counterexample (Max Talwar, 2026; graph6 `JBza_CB?wF_`):
an 11-vertex graph with `b = 8`, `f = 6`, `l = 2`. We verify `b ≥ 8`, `f ≤ 6`, `l ≤ 2`.

Remark on universes: the catalogue states the conjecture for `α : Type*`; we refute it for
`α : Type` (universe 0), which is where the counterexample lives.
-/

namespace OpenProblems.WOWII91

open Finset SimpleGraph

variable {α : Type} [Fintype α] [DecidableEq α]

/-! Definitions copied verbatim from `FormalConjecturesForMathlib`. -/

noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

noncomputable def b (G : SimpleGraph α) : ℝ := (largestInducedBipartiteSubgraphSize G : ℝ)

noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ := (indepNeighborsCard G v : ℝ)

noncomputable def averageIndepNeighbors (G : SimpleGraph α) : ℝ :=
  (∑ v ∈ Finset.univ, indepNeighbors G v) / (Fintype.card α : ℝ)

noncomputable abbrev l (G : SimpleGraph α) : ℝ := averageIndepNeighbors G

/-! ### The counterexample -/

/-- Edge list of graph6 `JBza_CB?wF_`. -/
def edges : List (ℕ × ℕ) :=
  [(0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (3, 6), (6, 7),
   (6, 8), (6, 9), (6, 10), (7, 8), (7, 9), (7, 10), (8, 9), (8, 10), (9, 10)]

def graph : SimpleGraph (Fin 11) where
  Adj i j := (i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun i j => by unfold graph; infer_instance

theorem graph_connected : graph.Connected := by
  have h0 : ∀ v : Fin 11, graph.Reachable 0 v := by
    have a : ∀ i j : Fin 11, (i.val, j.val) ∈ edges → graph.Reachable i j :=
      fun i j h => (show graph.Adj i j from Or.inl h).reachable
    have r4 := a 0 4 (by decide); have r5 := a 0 5 (by decide)
    have r1 := r4.trans (a 1 4 (by decide)).symm
    have r2 := r4.trans (a 2 4 (by decide)).symm
    have r3 := r1.trans (a 1 3 (by decide)); have r6 := r1.trans (a 1 6 (by decide))
    have r7 := r6.trans (a 6 7 (by decide)); have r8 := r6.trans (a 6 8 (by decide))
    have r9 := r6.trans (a 6 9 (by decide)); have r10 := r6.trans (a 6 10 (by decide))
    intro v; fin_cases v
    exacts [Reachable.refl _, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  exact ⟨fun u v => (h0 u).symm.trans (h0 v)⟩

/-! #### `b ≥ 8` -/

def bipSet : Finset (Fin 11) := {0, 1, 2, 3, 4, 5, 7, 8}
def bipColor : Fin 11 → Fin 2 := ![0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0]

theorem b_ge : (8 : ℝ) ≤ b graph := by
  have hcol : ∀ x y : Fin 11, x ∈ bipSet → y ∈ bipSet → graph.Adj x y → bipColor x ≠ bipColor y := by
    decide +kernel
  have hbip : (graph.induce (bipSet : Set (Fin 11))).IsBipartite :=
    ⟨Coloring.mk (fun v => bipColor v.1) fun {u v} h => hcol u v u.2 v.2 h⟩
  have : 8 ≤ largestInducedBipartiteSubgraphSize graph := by
    apply le_csSup ⟨11, by rintro n ⟨s, -, rfl⟩; exact s.card_le_univ.trans (by simp)⟩
    exact ⟨bipSet, hbip, by decide⟩
  unfold b; exact_mod_cast this

/-! #### `f ≤ 6` -/

theorem not_acyclic_of_triangle (S : Finset (Fin 11)) (hS : (graph.induce (S : Set (Fin 11))).IsAcyclic)
    (a b c : Fin 11) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : graph.Adj a b) (hbc : graph.Adj b c) (hca : graph.Adj c a) : False := by
  let va : (S : Set (Fin 11)) := ⟨a, ha⟩
  let vb : (S : Set (Fin 11)) := ⟨b, hb⟩
  let vc : (S : Set (Fin 11)) := ⟨c, hc⟩
  have h1 : (graph.induce (S : Set (Fin 11))).Adj va vb := hab
  have h2 : (graph.induce (S : Set (Fin 11))).Adj vb vc := hbc
  have h3 : (graph.induce (S : Set (Fin 11))).Adj vc va := hca
  exact hS (.cons h1 (.cons h2 (.cons h3 .nil))) (by
    rw [Walk.isCycle_def]
    refine ⟨?_, by simp, ?_⟩
    · rw [Walk.isTrail_def]
      simp [va, vb, vc, Sym2.eq_iff, hab.ne, hbc.ne, hca.ne, hab.ne.symm, hbc.ne.symm, hca.ne.symm]
    · simp [va, vb, vc, hab.ne.symm, hbc.ne, hca.ne])

theorem not_acyclic_of_square (S : Finset (Fin 11)) (hS : (graph.induce (S : Set (Fin 11))).IsAcyclic)
    (a b c d : Fin 11) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hac : a ≠ c) (hbd : b ≠ d)
    (hab : graph.Adj a b) (hbc : graph.Adj b c) (hcd : graph.Adj c d) (hda : graph.Adj d a) :
    False := by
  let va : (S : Set (Fin 11)) := ⟨a, ha⟩
  let vb : (S : Set (Fin 11)) := ⟨b, hb⟩
  let vc : (S : Set (Fin 11)) := ⟨c, hc⟩
  let vd : (S : Set (Fin 11)) := ⟨d, hd⟩
  have h1 : (graph.induce (S : Set (Fin 11))).Adj va vb := hab
  have h2 : (graph.induce (S : Set (Fin 11))).Adj vb vc := hbc
  have h3 : (graph.induce (S : Set (Fin 11))).Adj vc vd := hcd
  have h4 : (graph.induce (S : Set (Fin 11))).Adj vd va := hda
  exact hS (.cons h1 (.cons h2 (.cons h3 (.cons h4 .nil)))) (by
    rw [Walk.isCycle_def]
    refine ⟨?_, by simp, ?_⟩
    · rw [Walk.isTrail_def]
      simp [va, vb, vc, vd, Sym2.eq_iff, hab.ne, hbc.ne, hcd.ne, hda.ne, hab.ne.symm, hbc.ne.symm,
        hcd.ne.symm, hda.ne.symm, hac, hbd, hac.symm, hbd.symm]
    · simp [va, vb, vc, vd, hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac, hbd, hbd.symm, hac.symm])

/-- Triangles and 4-cycles of the graph, as triples/quadruples of vertex numbers. -/
def triangles : List (ℕ × ℕ × ℕ) :=
  [(1, 3, 6), (6, 7, 8), (6, 7, 9), (6, 7, 10), (6, 8, 9), (6, 8, 10), (6, 9, 10), (7, 8, 9),
   (7, 8, 10), (7, 9, 10), (8, 9, 10)]

def squares : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 4, 1, 5), (0, 4, 2, 5), (1, 3, 2, 4), (1, 3, 2, 5), (1, 4, 2, 5)]

/-- Adjacency on vertex numbers. -/
def adjN (i j : ℕ) : Prop := (i, j) ∈ edges ∨ (j, i) ∈ edges

instance : DecidableRel adjN := fun i j => by unfold adjN; infer_instance

theorem triangles_valid : ∀ t ∈ triangles, adjN t.1 t.2.1 ∧ adjN t.2.1 t.2.2 ∧ adjN t.2.2 t.1 := by
  decide

theorem squares_valid : ∀ q ∈ squares, q.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧
    adjN q.1 q.2.1 ∧ adjN q.2.1 q.2.2.1 ∧ adjN q.2.2.1 q.2.2.2 ∧ adjN q.2.2.2 q.1 := by
  decide

/-- Does the vertex list `L` contain one of the listed triangles or 4-cycles? -/
def hit (L : List ℕ) : Bool :=
  triangles.any (fun t => L.contains t.1 && L.contains t.2.1 && L.contains t.2.2) ||
  squares.any (fun q => L.contains q.1 && L.contains q.2.1 && L.contains q.2.2.1 &&
    L.contains q.2.2.2)

/-- Every 7 vertices `a > b > ⋯ > g` contain a listed triangle or 4-cycle. -/
def sevenCheck : Bool :=
  (List.range 11).all fun a => (List.range a).all fun b => (List.range b).all fun c =>
    (List.range c).all fun d => (List.range d).all fun e => (List.range e).all fun f =>
      (List.range f).all fun g => hit [a, b, c, d, e, f, g]

theorem sevenCheck_eq : sevenCheck = true := by decide +kernel

theorem seven_hit : ∀ a < 11, ∀ b < a, ∀ c < b, ∀ d < c, ∀ e < d, ∀ f < e, ∀ g < f,
    hit [a, b, c, d, e, f, g] = true := by
  have h := sevenCheck_eq
  simp only [sevenCheck, List.all_eq_true, List.mem_range] at h
  exact h

theorem forest_card_le (S : Finset (Fin 11)) (hS : (graph.induce (S : Set (Fin 11))).IsAcyclic) :
    S.card ≤ 6 := by
  by_contra h
  push_neg at h
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq (show 7 ≤ S.card by omega)
  obtain ⟨e, he, hmem⟩ : ∃ e : Fin 7 → Fin 11, StrictMono e ∧ ∀ i, e i ∈ T :=
    ⟨_, (T.orderEmbOfFin hT).strictMono, T.orderEmbOfFin_mem hT⟩
  have hh := seven_hit (e 6).val (e 6).isLt (e 5).val (he (by decide)) (e 4).val (he (by decide))
    (e 3).val (he (by decide)) (e 2).val (he (by decide)) (e 1).val (he (by decide))
    (e 0).val (he (by decide))
  set L := [(e 6).val, (e 5).val, (e 4).val, (e 3).val, (e 2).val, (e 1).val, (e 0).val] with hL
  have memL : ∀ m ∈ L, ∃ x ∈ S, x.val = m := by
    intro m hm
    simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, hTS (hmem _), rfl⟩
  have adj : ∀ x y : Fin 11, adjN x.val y.val → graph.Adj x y := fun _ _ h => h
  simp only [hit, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hh
  rcases hh with ⟨t, ht, ⟨h1, h2⟩, h3⟩ | ⟨q, hq, ⟨⟨h1, h2⟩, h3⟩, h4⟩
  · obtain ⟨a1, a2, a3⟩ := triangles_valid t ht
    obtain ⟨x, hx, hxv⟩ := memL _ h1
    obtain ⟨y, hy, hyv⟩ := memL _ h2
    obtain ⟨z, hz, hzv⟩ := memL _ h3
    rw [← hxv] at a1 a3; rw [← hyv] at a1 a2; rw [← hzv] at a2 a3
    exact not_acyclic_of_triangle S hS x y z hx hy hz (adj _ _ a1) (adj _ _ a2) (adj _ _ a3)
  · obtain ⟨n1, n2, a1, a2, a3, a4⟩ := squares_valid q hq
    obtain ⟨x, hx, hxv⟩ := memL _ h1
    obtain ⟨y, hy, hyv⟩ := memL _ h2
    obtain ⟨z, hz, hzv⟩ := memL _ h3
    obtain ⟨w, hw, hwv⟩ := memL _ h4
    rw [← hxv] at a1 a4 n1; rw [← hyv] at a1 a2 n2; rw [← hzv] at a2 a3 n1
    rw [← hwv] at a3 a4 n2
    exact not_acyclic_of_square S hS x y z w hx hy hz hw (fun h => n1 (congrArg Fin.val h))
      (fun h => n2 (congrArg Fin.val h)) (adj _ _ a1) (adj _ _ a2) (adj _ _ a3) (adj _ _ a4)

theorem f_le : largestInducedForestSize graph ≤ 6 := by
  apply csSup_le ⟨0, by refine ⟨∅, fun v => ?_, rfl⟩; exact absurd v.2 (by simp)⟩
  rintro n ⟨S, hS, rfl⟩
  exact forest_card_le S hS

/-! #### `l ≤ 2` -/



/-- Boolean check: no `2` indices below `n` are pairwise `R`-related. -/
def free2 (R : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  (List.range n).all fun a => (List.range a).all fun b => 
    !(R a b)

theorem false_of_free2 {n : ℕ} {R : ℕ → ℕ → Bool} {t : Finset (Fin n)} (ht : t.card = 2)
    (hR : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → R x y = true) (h : free2 R n = true) : False := by
  obtain ⟨e, he, hmem⟩ : ∃ e : Fin _ → Fin n, StrictMono e ∧ ∀ i, e i ∈ t :=
    ⟨_, (t.orderEmbOfFin ht).strictMono, t.orderEmbOfFin_mem ht⟩
  simp only [free2, List.all_eq_true, List.mem_range] at h
  have := h (e 1).val (e 1).isLt (e 0).val (he (by decide))
  simp [hR _ (hmem 1) _ (hmem 0) (he.injective.ne (by decide))] at this

/-- Boolean check: no `3` indices below `n` are pairwise `R`-related. -/
def free3 (R : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  (List.range n).all fun a => (List.range a).all fun b => (List.range b).all fun c => 
    !(R a b && R a c && R b c)

theorem false_of_free3 {n : ℕ} {R : ℕ → ℕ → Bool} {t : Finset (Fin n)} (ht : t.card = 3)
    (hR : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → R x y = true) (h : free3 R n = true) : False := by
  obtain ⟨e, he, hmem⟩ : ∃ e : Fin _ → Fin n, StrictMono e ∧ ∀ i, e i ∈ t :=
    ⟨_, (t.orderEmbOfFin ht).strictMono, t.orderEmbOfFin_mem ht⟩
  simp only [free3, List.all_eq_true, List.mem_range] at h
  have := h (e 2).val (e 2).isLt (e 1).val (he (by decide)) (e 0).val (he (by decide))
  simp [hR _ (hmem 2) _ (hmem 1) (he.injective.ne (by decide)), hR _ (hmem 2) _ (hmem 0) (he.injective.ne (by decide)), hR _ (hmem 1) _ (hmem 0) (he.injective.ne (by decide))] at this

/-- Boolean check: no `4` indices below `n` are pairwise `R`-related. -/
def free4 (R : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  (List.range n).all fun a => (List.range a).all fun b => (List.range b).all fun c => (List.range c).all fun d => 
    !(R a b && R a c && R a d && R b c && R b d && R c d)

theorem false_of_free4 {n : ℕ} {R : ℕ → ℕ → Bool} {t : Finset (Fin n)} (ht : t.card = 4)
    (hR : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → R x y = true) (h : free4 R n = true) : False := by
  obtain ⟨e, he, hmem⟩ : ∃ e : Fin _ → Fin n, StrictMono e ∧ ∀ i, e i ∈ t :=
    ⟨_, (t.orderEmbOfFin ht).strictMono, t.orderEmbOfFin_mem ht⟩
  simp only [free4, List.all_eq_true, List.mem_range] at h
  have := h (e 3).val (e 3).isLt (e 2).val (he (by decide)) (e 1).val (he (by decide)) (e 0).val (he (by decide))
  simp [hR _ (hmem 3) _ (hmem 2) (he.injective.ne (by decide)), hR _ (hmem 3) _ (hmem 1) (he.injective.ne (by decide)), hR _ (hmem 3) _ (hmem 0) (he.injective.ne (by decide)), hR _ (hmem 2) _ (hmem 1) (he.injective.ne (by decide)), hR _ (hmem 2) _ (hmem 0) (he.injective.ne (by decide)), hR _ (hmem 1) _ (hmem 0) (he.injective.ne (by decide))] at this

def indepBound : Fin 11 → ℕ := ![2, 3, 3, 2, 3, 3, 2, 1, 1, 1, 1]

/-- `R_v a b`: `a, b` are non-adjacent neighbours of `v`. -/
def indepRel (v : ℕ) (a b : ℕ) : Bool := decide (adjN v a) && decide (adjN v b) && !decide (adjN a b)

/-- No independent set of size `indepBound v + 1` inside the neighbourhood of `v`. -/
theorem indep_free : ∀ v : Fin 11,
    (indepBound v = 1 → free2 (indepRel v) 11 = true) ∧
    (indepBound v = 2 → free3 (indepRel v) 11 = true) ∧
    (indepBound v = 3 → free4 (indepRel v) 11 = true) := by
  decide +kernel

theorem indep_check (v : Fin 11) (t : Finset (Fin 11)) (ht : ∀ x ∈ t, graph.Adj v x)
    (hind : ∀ x ∈ t, ∀ y ∈ t, ¬ graph.Adj x y) : t.card ≤ indepBound v := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨u, hut, hu⟩ := exists_subset_card_eq (show indepBound v + 1 ≤ t.card by omega)
  have hR : ∀ x ∈ u, ∀ y ∈ u, x ≠ y → indepRel v x y = true := by
    intro x hx y hy _
    simp only [indepRel, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨⟨ht x (hut hx), ht y (hut hy)⟩, hind x (hut hx) y (hut hy)⟩
  have hb : indepBound v = 1 ∨ indepBound v = 2 ∨ indepBound v = 3 := by
    fin_cases v <;> simp [indepBound]
  obtain ⟨f1, f2, f3⟩ := indep_free v
  rcases hb with hb | hb | hb <;> rw [hb] at hu
  · exact false_of_free2 hu hR (f1 hb)
  · exact false_of_free3 hu hR (f2 hb)
  · exact false_of_free4 hu hR (f3 hb)

theorem indepNeighborsCard_le (v : Fin 11) : indepNeighborsCard graph v ≤ indepBound v := by
  unfold indepNeighborsCard
  obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := graph.induce (graph.neighborSet v))
  rw [← hs.card_eq]
  set t := s.map (Function.Embedding.subtype _)
  have hct : t.card = s.card := card_map _
  rw [← hct]
  apply indep_check v t
  · intro x hx
    obtain ⟨y, -, rfl⟩ := mem_map.1 hx
    exact y.2
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := mem_map.1 hy
    have hne : x' ≠ y' := fun h => hxy.ne (by rw [h])
    exact hs.isIndepSet hx' hy' hne hxy

theorem l_le : l graph ≤ 2 := by
  unfold l averageIndepNeighbors indepNeighbors
  rw [Fintype.card_fin, div_le_iff₀ (by norm_num)]
  have hsum : ∑ v : Fin 11, indepNeighborsCard graph v ≤ ∑ v : Fin 11, indepBound v :=
    sum_le_sum fun v _ => indepNeighborsCard_le v
  have h22 : ∑ v : Fin 11, indepBound v = 22 := by decide
  rw [h22] at hsum
  have : (∑ v : Fin 11, (indepNeighborsCard graph v : ℝ)) ≤ 22 := by exact_mod_cast hsum
  norm_num; linarith

/-- **First formal refutation of WOWII Conjecture 91.** -/
theorem conjecture91_false :
    ¬ ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α],
      ∀ (G : SimpleGraph α) (_ : G.Connected),
        b G ≤ 1 + (largestInducedForestSize G : ℝ) * ⌈l G⌉ / 2 := by
  intro h
  have h1 := h graph graph_connected
  have hb := b_ge
  have hf : (largestInducedForestSize graph : ℝ) ≤ 6 := by exact_mod_cast f_le
  have hc : (⌈l graph⌉ : ℝ) ≤ 2 := by exact_mod_cast Int.ceil_le.2 (by exact_mod_cast l_le)
  have hf0 : (0 : ℝ) ≤ largestInducedForestSize graph := by positivity
  have : (largestInducedForestSize graph : ℝ) * ⌈l graph⌉ ≤ 12 := by
    calc (largestInducedForestSize graph : ℝ) * ⌈l graph⌉
        ≤ (largestInducedForestSize graph : ℝ) * 2 := mul_le_mul_of_nonneg_left hc hf0
      _ ≤ 12 := by linarith
  linarith

end OpenProblems.WOWII91
