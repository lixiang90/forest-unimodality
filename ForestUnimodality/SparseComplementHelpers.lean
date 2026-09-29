import ForestUnimodality.MaximumIndependent
import ForestUnimodality.EdgeLowerBound
import ForestUnimodality.EdgeCounting
import ForestUnimodality.PrivateNeighborBound
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Crossing-edge blocks and their independent-set exchange operation.
These lemmas prove the exchange itself; they do not assume it as a property
of an abstract block. -/

namespace ForestUnimodality

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- The graph retaining precisely the edges crossing the partition I / (S-I). -/
def crossingGraph (G : SimpleGraph V) (S I : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S ∧
    ((x ∈ I ∧ y ∉ I) ∨ (y ∈ I ∧ x ∉ I))
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1.ne rfl⟩

/-- A crossing-edge component, recorded as a finite subset of S. -/
noncomputable def crossingBlock (G : SimpleGraph V) (S I : Finset V) (r : V) : Finset V := by
  classical
  exact S.filter fun x => (crossingGraph G S I).Reachable r x

@[simp] theorem mem_crossingBlock {G : SimpleGraph V} {S I : Finset V} {r x : V} :
    x ∈ crossingBlock G S I r ↔ x ∈ S ∧ (crossingGraph G S I).Reachable r x := by
  classical
  simp [crossingBlock]

theorem crossingBlock_subset (G : SimpleGraph V) (S I : Finset V) (r : V) :
    crossingBlock G S I r ⊆ S := by
  intro x hx
  exact (mem_crossingBlock.mp hx).1

theorem crossingBlock_closed {G : SimpleGraph V} {S I : Finset V} {r x y : V}
    (hx : x ∈ crossingBlock G S I r) (hy : y ∈ S) (hxy : G.Adj x y)
    (hcross : (x ∈ I ∧ y ∉ I) ∨ (y ∈ I ∧ x ∉ I)) :
    y ∈ crossingBlock G S I r := by
  obtain ⟨hxS, hreach⟩ := mem_crossingBlock.mp hx
  have he : (crossingGraph G S I).Adj x y := ⟨hxy, hxS, hy, hcross⟩
  exact mem_crossingBlock.mpr ⟨hy, hreach.trans he.reachable⟩

/-- A forest edge outside the crossing graph cannot join two vertices of one
crossing block: it would supply a second connection across a bridge. -/
theorem crossingBlock_no_internal_complement_edge
    {G : SimpleGraph V} {S I : Finset V} {r x y : V} (hG : G.IsAcyclic)
    (hx : x ∈ crossingBlock G S I r) (hy : y ∈ crossingBlock G S I r)
    (hxI : x ∉ I) (hyI : y ∉ I) : ¬G.Adj x y := by
  intro hxy
  have hreach : (crossingGraph G S I).Reachable x y :=
    (mem_crossingBlock.mp hx).2.symm.trans (mem_crossingBlock.mp hy).2
  have hle : crossingGraph G S I ≤ G.deleteEdges {s(x, y)} := by
    intro a b hab
    apply deleteEdges_adj.mpr
    refine ⟨hab.1, ?_⟩
    intro he
    have heq : s(a, b) = s(x, y) := Set.mem_singleton_iff.mp he
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hab.2.2.2 with h | h <;> simp_all
  exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hG hxy))
    (hreach.mono hle)

/-- Exchange selected and unselected vertices in a finite block. -/
def exchangeBlock (I B : Finset V) : Finset V := (I \ B) ∪ (B \ I)

/-- Flipping a crossing block of a forest preserves independence. -/
theorem exchange_crossingBlock_mem_independentSubsets
    {G : SimpleGraph V} {S I : Finset V} (hG : G.IsAcyclic)
    (hI : I ∈ independentSubsets G S) (r : V) :
    exchangeBlock I (crossingBlock G S I r) ∈ independentSubsets G S := by
  obtain ⟨hIS, hII⟩ := mem_independentSubsets.mp hI
  have hBS := crossingBlock_subset G S I r
  apply mem_independentSubsets.mpr
  refine ⟨union_subset (sdiff_subset.trans hIS) (sdiff_subset.trans hBS), ?_⟩
  intro x hx y hy hne hxy
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
  · exact hII (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1 hne hxy
  · obtain ⟨hxI, hxB⟩ := mem_sdiff.mp hx
    obtain ⟨hyB, hyI⟩ := mem_sdiff.mp hy
    exact hxB (crossingBlock_closed hyB (hIS hxI) hxy.symm (Or.inr ⟨hxI, hyI⟩))
  · obtain ⟨hxB, hxI⟩ := mem_sdiff.mp hx
    obtain ⟨hyI, hyB⟩ := mem_sdiff.mp hy
    exact hyB (crossingBlock_closed hxB (hIS hyI) hxy (Or.inr ⟨hyI, hxI⟩))
  · obtain ⟨hxB, hxI⟩ := mem_sdiff.mp hx
    obtain ⟨hyB, hyI⟩ := mem_sdiff.mp hy
    exact crossingBlock_no_internal_complement_edge hG hxB hyB hxI hyI hxy

theorem exchangeBlock_card (I B : Finset V) :
    (exchangeBlock I B).card + (I ∩ B).card = I.card + (B \ I).card := by
  have hd : Disjoint (I \ B) (B \ I) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1
  rw [exchangeBlock, card_union_of_disjoint hd]
  have hcard := card_sdiff_add_card_inter I B
  omega

/-- Maximum cardinality alone makes every crossing block's selected side at
least as large as its unselected side. -/
theorem IsMaximumIndependentOn.crossingBlock_card_le
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic) (r : V) :
    (crossingBlock G S I r \ I).card ≤ (I ∩ crossingBlock G S I r).card := by
  have hbound := hI.2 _ (exchange_crossingBlock_mem_independentSubsets hG hI.1 r)
  have hcard := exchangeBlock_card I (crossingBlock G S I r)
  omega

/-- An edge in the new complement already belonged to the old complement. -/
theorem exchange_crossingBlock_complement_adj_old
    {G : SimpleGraph V} {S I : Finset V} {r x y : V}
    (hI : I ∈ independentSubsets G S)
    (hx : x ∈ S \ exchangeBlock I (crossingBlock G S I r))
    (hy : y ∈ S \ exchangeBlock I (crossingBlock G S I r)) (hxy : G.Adj x y) :
    x ∈ S \ I := by
  obtain ⟨hIS, hII⟩ := mem_independentSubsets.mp hI
  obtain ⟨hxS, hxnew⟩ := mem_sdiff.mp hx
  obtain ⟨hyS, hynew⟩ := mem_sdiff.mp hy
  refine mem_sdiff.mpr ⟨hxS, ?_⟩
  intro hxI
  have hxB : x ∈ crossingBlock G S I r := by
    by_contra hn
    exact hxnew (mem_union_left _ (mem_sdiff.mpr ⟨hxI, hn⟩))
  have hyI : y ∉ I := fun hyI => hII hxI hyI hxy.ne hxy
  have hyB := crossingBlock_closed hxB hyS hxy (Or.inl ⟨hxI, hyI⟩)
  exact hynew (mem_union_right _ (mem_sdiff.mpr ⟨hyB, hyI⟩))

theorem exchange_crossingBlock_edgePairs_subset
    {G : SimpleGraph V} {S I : Finset V}
    (hI : I ∈ independentSubsets G S) (r : V) :
    edgePairsOn G (S \ exchangeBlock I (crossingBlock G S I r)) ⊆
      edgePairsOn G (S \ I) := by
  intro E hE
  obtain ⟨hES, hc, hbad⟩ := mem_edgePairsOn.mp hE
  have hex : ∃ x ∈ E, ∃ y ∈ E, G.Adj x y := by
    by_contra hn
    apply hbad
    intro x hx y hy _ hxy
    exact hn ⟨x, hx, y, hy, hxy⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hex
  have hp : ({x, y} : Finset V) = E := by
    apply eq_of_subset_of_card_le
    · exact insert_subset hx (singleton_subset_iff.mpr hy)
    · simp [hc, hxy.ne]
  refine mem_edgePairsOn.mpr ⟨?_, hc, hbad⟩
  rw [← hp]
  exact insert_subset (exchange_crossingBlock_complement_adj_old hI (hES hx) (hES hy) hxy)
    (singleton_subset_iff.mpr
      (exchange_crossingBlock_complement_adj_old hI (hES hy) (hES hx) hxy.symm))

/-- Every boundary edge of a crossing block has two unselected endpoints. -/
theorem crossingBlock_boundary_not_mem
    {G : SimpleGraph V} {S I : Finset V} {r x y : V}
    (hI : I ∈ independentSubsets G S) (hx : x ∈ crossingBlock G S I r)
    (hy : y ∈ S) (hyB : y ∉ crossingBlock G S I r) (hxy : G.Adj x y) :
    x ∉ I ∧ y ∉ I := by
  have hII := (mem_independentSubsets.mp hI).2
  have hxI : x ∉ I := by
    intro hxI
    have hyI : y ∉ I := fun hyI => hII hxI hyI hxy.ne hxy
    exact hyB (crossingBlock_closed hx hy hxy (Or.inl ⟨hxI, hyI⟩))
  refine ⟨hxI, ?_⟩
  intro hyI
  exact hyB (crossingBlock_closed hx hy hxy (Or.inr ⟨hyI, hxI⟩))

/-- If a block has a boundary edge, its flip strictly reduces complement edges. -/
theorem exchange_crossingBlock_edgeCount_lt
    {G : SimpleGraph V} {S I : Finset V} {r x y : V}
    (hI : I ∈ independentSubsets G S) (hx : x ∈ crossingBlock G S I r)
    (hy : y ∈ S) (hyB : y ∉ crossingBlock G S I r) (hxy : G.Adj x y) :
    edgeCountOn G (S \ exchangeBlock I (crossingBlock G S I r)) <
      edgeCountOn G (S \ I) := by
  classical
  have hnot := crossingBlock_boundary_not_mem hI hx hy hyB hxy
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨exchange_crossingBlock_edgePairs_subset hI r, ?_⟩
  intro heq
  have hp : ({x, y} : Finset V) ∈ edgePairsOn G (S \ I) := by
    apply mem_edgePairsOn.mpr
    refine ⟨insert_subset (mem_sdiff.mpr ⟨(mem_crossingBlock.mp hx).1, hnot.1⟩)
      (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨hy, hnot.2⟩)), ?_, ?_⟩
    · simp [hxy.ne]
    · intro hind
      exact hind (by simp) (by simp) hxy.ne hxy
  rw [← heq] at hp
  have hxnew := (mem_edgePairsOn.mp hp).1 (by simp : x ∈ ({x, y} : Finset V))
  exact (mem_sdiff.mp hxnew).2 (mem_union_right _ (mem_sdiff.mpr ⟨hx, hnot.1⟩))

theorem crossingGraph_reachable_mem
    {G : SimpleGraph V} {S I : Finset V} {r x : V} (hr : r ∈ S)
    (hx : (crossingGraph G S I).Reachable r x) : x ∈ S := by
  obtain ⟨p⟩ := hx
  induction p with
  | nil => exact hr
  | cons h p ih => exact ih h.2.2.1

/-- The finite block is the whole crossing component when its root is in S. -/
theorem coe_crossingBlock_eq_supp
    (G : SimpleGraph V) (S I : Finset V) {r : V} (hr : r ∈ S) :
    (↑(crossingBlock G S I r) : Set V) =
      ((crossingGraph G S I).connectedComponentMk r).supp := by
  ext x
  simp only [mem_coe, mem_crossingBlock, ConnectedComponent.mem_supp_iff,
    ConnectedComponent.eq, reachable_comm]
  exact ⟨fun h => h.2, fun h => ⟨crossingGraph_reachable_mem hr h, h⟩⟩

/-- Each nonempty crossing block induces a connected original subgraph. -/
theorem connected_induce_crossingBlock
    (G : SimpleGraph V) (S I : Finset V) {r : V} (hr : r ∈ S) :
    (G.induce (↑(crossingBlock G S I r) : Set V)).Connected := by
  rw [coe_crossingBlock_eq_supp G S I hr]
  have hc := ((crossingGraph G S I).connectedComponentMk r).connected_toSimpleGraph
  apply hc.mono
  intro x y hxy
  exact hxy.1

/-- The internal edges of a crossing block pay for all but one of its vertices.
This is the local count needed to avoid constructing a contracted quotient graph. -/
theorem crossingBlock_card_le_edgeCount_add_one
    (G : SimpleGraph V) (S I : Finset V) {r : V} (hr : r ∈ S) :
    (crossingBlock G S I r).card ≤ edgeCountOn G (crossingBlock G S I r) + 1 := by
  classical
  have h := (connected_induce_crossingBlock G S I hr).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card, ← edgeCountOn_eq_card_edgeFinset_induce] at h
  simpa using h

theorem edgePairsOn_exists_adj_pair
    {G : SimpleGraph V} {S E : Finset V} (hE : E ∈ edgePairsOn G S) :
    ∃ x ∈ S, ∃ y ∈ S, G.Adj x y ∧ E = {x, y} := by
  obtain ⟨hES, hc, hbad⟩ := mem_edgePairsOn.mp hE
  have hex : ∃ x ∈ E, ∃ y ∈ E, G.Adj x y := by
    by_contra hn
    apply hbad
    intro x hx y hy _ hxy
    exact hn ⟨x, hx, y, hy, hxy⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hex
  refine ⟨x, hES hx, y, hES hy, hxy, ?_⟩
  symm
  apply eq_of_subset_of_card_le
  · exact insert_subset hx (singleton_subset_iff.mpr hy)
  · simp [hc, hxy.ne]

theorem edgeCountOn_add_one_le_card_of_nonempty
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S : Finset V} (hS : S.Nonempty) :
    edgeCountOn G S + 1 ≤ S.card := by
  classical
  letI : Nonempty (↑S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  rw [edgeCountOn_eq_card_edgeFinset_induce]
  simpa using forest_card_edges_add_one_le (G.induce (↑S : Set V))
    (hG.induce (↑S : Set V))

#print axioms crossingBlock_no_internal_complement_edge
#print axioms exchange_crossingBlock_mem_independentSubsets
#print axioms IsMaximumIndependentOn.crossingBlock_card_le
#print axioms exchange_crossingBlock_edgeCount_lt
#print axioms crossingBlock_card_le_edgeCount_add_one

end ForestUnimodality
