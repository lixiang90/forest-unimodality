import ForestUnimodality.SparseComplementHelpers

/-!
Sparse-complement selection for forests. Minimize complement edges among the
maximum independent subsets, and exchange crossing-edge components. Every
component with a boundary then has positive selected/unselected surplus.
Packing the internal block edges and complement edges into an induced forest
gives the global bound without contracting the graph or assuming a block theorem.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- Maximum independent cardinality, followed by minimum complement edges. -/
def IsEdgeMinimalMaximumOn (G : SimpleGraph V) (S I : Finset V) : Prop :=
  IsMaximumIndependentOn G S I ∧
    ∀ K : Finset V, IsMaximumIndependentOn G S K →
      edgeCountOn G (S \ I) ≤ edgeCountOn G (S \ K)

/-- The finite minimization is an actual existence theorem, with no choice of
a special maximum independent subset left as an assumption. -/
theorem exists_edgeMinimalMaximumOn (G : SimpleGraph V) (S : Finset V) :
    ∃ I : Finset V, IsEdgeMinimalMaximumOn G S I := by
  classical
  obtain ⟨I, hI⟩ := exists_maximumIndependentOn G S
  let candidates := (independentSubsets G S).filter fun K => IsMaximumIndependentOn G S K
  have hnonempty : candidates.Nonempty := ⟨I, mem_filter.mpr ⟨hI.1, hI⟩⟩
  obtain ⟨J, hJ, hmin⟩ := candidates.exists_min_image
    (fun K => edgeCountOn G (S \ K)) hnonempty
  refine ⟨J, (mem_filter.mp hJ).2, ?_⟩
  intro K hK
  exact hmin K (mem_filter.mpr ⟨hK.1, hK⟩)

/-- For the minimizing choice, every crossing component incident with a
complement edge contains strictly more selected than unselected vertices. -/
theorem IsEdgeMinimalMaximumOn.crossingBlock_card_lt_of_boundary
    {G : SimpleGraph V} {S I : Finset V} {r x y : V}
    (hI : IsEdgeMinimalMaximumOn G S I) (hG : G.IsAcyclic)
    (hx : x ∈ crossingBlock G S I r) (hy : y ∈ S)
    (hyB : y ∉ crossingBlock G S I r) (hxy : G.Adj x y) :
    (crossingBlock G S I r \ I).card < (I ∩ crossingBlock G S I r).card := by
  have hle := hI.1.crossingBlock_card_le hG r
  by_contra hnot
  have heq : (crossingBlock G S I r \ I).card =
      (I ∩ crossingBlock G S I r).card := by omega
  have hcard := exchangeBlock_card I (crossingBlock G S I r)
  have hexchange : (exchangeBlock I (crossingBlock G S I r)).card = I.card := by omega
  have hmax : IsMaximumIndependentOn G S (exchangeBlock I (crossingBlock G S I r)) := by
    refine ⟨exchange_crossingBlock_mem_independentSubsets hG hI.1.1 r, ?_⟩
    intro K hK
    rw [hexchange]
    exact hI.1.2 K hK
  have hmin := hI.2 _ hmax
  have hlt := exchange_crossingBlock_edgeCount_lt hI.1.1 hx hy hyB hxy
  exact (not_lt_of_ge hmin) hlt

/-- The selected subset and the strict boundary-block property are obtained
together, so subsequent structural rows can use this same fixed subset. -/
theorem exists_maximumIndependentOn_with_positive_boundary_blocks
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) :
    ∃ I : Finset V, IsMaximumIndependentOn G S I ∧
      ∀ (r x y : V), x ∈ crossingBlock G S I r → y ∈ S →
        y ∉ crossingBlock G S I r → G.Adj x y →
        (crossingBlock G S I r \ I).card < (I ∩ crossingBlock G S I r).card := by
  obtain ⟨I, hI⟩ := exists_edgeMinimalMaximumOn G S
  exact ⟨I, hI.1, fun r x y hx hy hyB hxy =>
    hI.crossingBlock_card_lt_of_boundary hG hx hy hyB hxy⟩

attribute [local instance] Classical.propDecidable

/-- The crossing components which occur in the finite ambient set. -/
noncomputable def crossingComponentsOn (G : SimpleGraph V) (S I : Finset V) :
    Finset (crossingGraph G S I).ConnectedComponent :=
  S.image (crossingGraph G S I).connectedComponentMk

/-- A crossing component has a boundary if an original edge leaves it within S. -/
def IsBoundaryCrossingComponent (G : SimpleGraph V) (S I : Finset V)
    (c : (crossingGraph G S I).ConnectedComponent) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, (crossingGraph G S I).connectedComponentMk x = c ∧
    (crossingGraph G S I).connectedComponentMk y ≠ c ∧ G.Adj x y

noncomputable def boundaryCrossingComponents (G : SimpleGraph V) (S I : Finset V) :
    Finset (crossingGraph G S I).ConnectedComponent := by
  classical
  exact (crossingComponentsOn G S I).filter (IsBoundaryCrossingComponent G S I)

theorem filter_component_eq_crossingBlock
    (G : SimpleGraph V) (S I : Finset V) (r : V) :
    (S.filter fun x => (crossingGraph G S I).connectedComponentMk x =
      (crossingGraph G S I).connectedComponentMk r) = crossingBlock G S I r := by
  classical
  ext x
  simp only [mem_filter, mem_crossingBlock, SimpleGraph.ConnectedComponent.eq,
    SimpleGraph.reachable_comm]

/-- The componentwise strict surplus bounds the number of boundary blocks by
the total selected/unselected cardinality difference. This count needs no
quotient-graph construction. -/
theorem IsEdgeMinimalMaximumOn.card_boundaryCrossingComponents_le
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsEdgeMinimalMaximumOn G S I) (hG : G.IsAcyclic) :
    (boundaryCrossingComponents G S I).card ≤ I.card - (S \ I).card := by
  classical
  let f := (crossingGraph G S I).connectedComponentMk
  let C := crossingComponentsOn G S I
  have hcover (T : Finset V) (hT : T ⊆ S) :
      ∀ x ∈ T, f x ∈ C := by
    intro x hx
    exact mem_image_of_mem f (hT hx)
  have hsum (T : Finset V) (hT : T ⊆ S) :
      (∑ c ∈ C, (T.filter fun x => f x = c).card) = T.card := by
    simpa using sum_fiberwise_of_maps_to (hcover T hT) (fun _ => (1 : ℕ))
  have hpoint : ∀ c ∈ C,
      ((S \ I).filter fun x => f x = c).card +
        (if IsBoundaryCrossingComponent G S I c then 1 else 0) ≤
          (I.filter fun x => f x = c).card := by
    intro c hc
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hc
    have hIeq : (I.filter fun x => f x = f r) = I ∩ crossingBlock G S I r := by
      rw [← filter_component_eq_crossingBlock]
      ext x
      simp only [mem_filter, mem_inter, f]
      exact ⟨fun h => ⟨h.1, hI.1.subset h.1, h.2⟩,
        fun h => ⟨h.1, h.2.2⟩⟩
    have hYeq : ((S \ I).filter fun x => f x = f r) = crossingBlock G S I r \ I := by
      rw [← filter_component_eq_crossingBlock]
      ext x
      simp only [mem_filter, mem_sdiff, f]
      tauto
    rw [hIeq, hYeq]
    by_cases hb : IsBoundaryCrossingComponent G S I (f r)
    · rw [if_pos hb]
      obtain ⟨x, hx, y, hy, hfx, hfy, hxy⟩ := hb
      have hxB : x ∈ crossingBlock G S I r := by
        rw [← filter_component_eq_crossingBlock]
        exact mem_filter.mpr ⟨hx, hfx⟩
      have hyB : y ∉ crossingBlock G S I r := by
        rw [← filter_component_eq_crossingBlock]
        intro hyB
        exact hfy (mem_filter.mp hyB).2
      exact hI.crossingBlock_card_lt_of_boundary hG hxB hy hyB hxy
    · rw [if_neg hb, add_zero]
      exact hI.1.crossingBlock_card_le hG r
  have hbound := sum_le_sum hpoint
  rw [sum_add_distrib, hsum (S \ I) sdiff_subset, hsum I hI.1.subset] at hbound
  have hcount : (∑ c ∈ C, if IsBoundaryCrossingComponent G S I c then 1 else 0) =
      (boundaryCrossingComponents G S I).card := by
    simp [boundaryCrossingComponents, C]
  rw [hcount] at hbound
  omega

/-- In a forest, the complement edges are fewer than their incident crossing
blocks. The proof packs the internal block edges together with the complement
edges into one induced forest; no acyclicity of a quotient graph is assumed. -/
theorem edgeCountOn_complement_le_boundaryCrossingComponents_sub_one
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S I : Finset V) :
    edgeCountOn G (S \ I) ≤ (boundaryCrossingComponents G S I).card - 1 := by
  classical
  let f := (crossingGraph G S I).connectedComponentMk
  let Q := boundaryCrossingComponents G S I
  let B : (crossingGraph G S I).ConnectedComponent → Finset V :=
    fun c => S.filter fun x => f x = c
  let U := Q.biUnion B
  have hBdis : (↑Q : Set (crossingGraph G S I).ConnectedComponent).PairwiseDisjoint B := by
    intro c hc d hd hne
    apply Finset.disjoint_left.mpr
    intro x hxc hxd
    exact hne ((mem_filter.mp hxc).2.symm.trans (mem_filter.mp hxd).2)
  have hBsub (c) (hc : c ∈ Q) : B c ⊆ U := by
    intro x hx
    exact mem_biUnion.mpr ⟨c, hc, hx⟩
  have hBroot (c) (hc : c ∈ Q) : ∃ r ∈ S, B c = crossingBlock G S I r := by
    obtain ⟨r, hr, rfl⟩ := mem_image.mp (mem_filter.mp hc).1
    exact ⟨r, hr, filter_component_eq_crossingBlock G S I r⟩
  have hBcount (c) (hc : c ∈ Q) : (B c).card ≤ edgeCountOn G (B c) + 1 := by
    obtain ⟨r, hr, heq⟩ := hBroot c hc
    rw [heq]
    exact crossingBlock_card_le_edgeCount_add_one G S I hr
  have hboundary {x y : V} (hx : x ∈ S \ I) (hy : y ∈ S \ I) (hxy : G.Adj x y) :
      f x ∈ Q := by
    have hxS := (mem_sdiff.mp hx).1
    have hyS := (mem_sdiff.mp hy).1
    have hne : f y ≠ f x := by
      intro heq
      have hxB : x ∈ crossingBlock G S I x := mem_crossingBlock.mpr ⟨hxS, .rfl⟩
      have hyB : y ∈ crossingBlock G S I x := by
        rw [← filter_component_eq_crossingBlock]
        exact mem_filter.mpr ⟨hyS, heq⟩
      exact crossingBlock_no_internal_complement_edge hG hxB hyB
        (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).2 hxy
    apply mem_filter.mpr
    refine ⟨mem_image_of_mem f hxS, ?_⟩
    exact ⟨x, hxS, y, hyS, rfl, hne, hxy⟩
  have hYedges : edgePairsOn G (S \ I) ⊆ edgePairsOn G U := by
    intro E hE
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := edgePairsOn_exists_adj_pair hE
    apply mem_edgePairsOn.mpr
    refine ⟨?_, by simp [hxy.ne], ?_⟩
    · apply insert_subset
      · exact hBsub (f x) (hboundary hx hy hxy) (mem_filter.mpr ⟨(mem_sdiff.mp hx).1, rfl⟩)
      · apply singleton_subset_iff.mpr
        exact hBsub (f y) (hboundary hy hx hxy.symm)
          (mem_filter.mpr ⟨(mem_sdiff.mp hy).1, rfl⟩)
    · intro hind
      exact hind (by simp) (by simp) hxy.ne hxy
  have hEdis : (↑Q : Set (crossingGraph G S I).ConnectedComponent).PairwiseDisjoint
      (fun c => edgePairsOn G (B c)) := by
    intro c hc d hd hne
    apply Finset.disjoint_left.mpr
    intro E hEc hEd
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := edgePairsOn_exists_adj_pair hEc
    have hxd := (mem_edgePairsOn.mp hEd).1 (by simp : x ∈ ({x, y} : Finset V))
    exact Finset.disjoint_left.mp (hBdis hc hd hne) hx hxd
  have hYEdis : Disjoint (edgePairsOn G (S \ I))
      (Q.biUnion fun c => edgePairsOn G (B c)) := by
    apply Finset.disjoint_left.mpr
    intro E hEY hEB
    obtain ⟨c, hc, hEc⟩ := mem_biUnion.mp hEB
    obtain ⟨r, hr, heq⟩ := hBroot c hc
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := edgePairsOn_exists_adj_pair hEY
    have hxB := (mem_edgePairsOn.mp hEc).1 (by simp : x ∈ ({x, y} : Finset V))
    have hyB := (mem_edgePairsOn.mp hEc).1 (by simp : y ∈ ({x, y} : Finset V))
    rw [heq] at hxB hyB
    exact crossingBlock_no_internal_complement_edge hG hxB hyB
      (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).2 hxy
  have hpack : edgeCountOn G (S \ I) + (∑ c ∈ Q, edgeCountOn G (B c)) ≤
      edgeCountOn G U := by
    have hsub : edgePairsOn G (S \ I) ∪
        (Q.biUnion fun c => edgePairsOn G (B c)) ⊆ edgePairsOn G U := by
      apply union_subset hYedges
      intro E hE
      obtain ⟨c, hc, hEc⟩ := mem_biUnion.mp hE
      exact edgePairsOn_mono G (hBsub c hc) hEc
    have hc := card_le_card hsub
    rw [card_union_of_disjoint hYEdis, card_biUnion hEdis] at hc
    exact hc
  have hvertices : U.card ≤ (∑ c ∈ Q, edgeCountOn G (B c)) + Q.card := by
    have hsum := sum_le_sum hBcount
    rw [← card_biUnion hBdis, sum_add_distrib] at hsum
    simpa only [sum_const, smul_eq_mul, mul_one] using hsum
  by_cases hz : edgeCountOn G (S \ I) = 0
  · rw [hz]
    exact Nat.zero_le _
  · have hUnonempty : U.Nonempty := by
      have hEY : (edgePairsOn G (S \ I)).Nonempty := card_pos.mp (Nat.pos_of_ne_zero hz)
      obtain ⟨E, hE⟩ := hEY
      obtain ⟨x, hx, y, hy, hxy, heq⟩ := edgePairsOn_exists_adj_pair (hYedges hE)
      exact ⟨x, hx⟩
    have hforest := edgeCountOn_add_one_le_card_of_nonempty hG hUnonempty
    change edgeCountOn G (S \ I) ≤ Q.card - 1
    omega

/-- An edge-minimizing maximum independent subset has the sparse complement
required by the structural finite-certificate rows. -/
theorem IsEdgeMinimalMaximumOn.edgeCountOn_complement_le
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsEdgeMinimalMaximumOn G S I) (hG : G.IsAcyclic) :
    edgeCountOn G (S \ I) ≤ I.card - (S \ I).card - 1 := by
  have hblocks := hI.card_boundaryCrossingComponents_le hG
  have hedges := edgeCountOn_complement_le_boundaryCrossingComponents_sub_one G hG S I
  exact hedges.trans (Nat.sub_le_sub_right hblocks 1)

/-- Sparse-complement selection for every finite induced forest, including
empty forests and forests of zero independence surplus. -/
theorem exists_maximumIndependentOn_sparse_complement
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) :
    ∃ I : Finset V, IsMaximumIndependentOn G S I ∧
      edgeCountOn G (S \ I) ≤ I.card - (S \ I).card - 1 := by
  obtain ⟨I, hI⟩ := exists_edgeMinimalMaximumOn G S
  exact ⟨I, hI.1, hI.edgeCountOn_complement_le hG⟩

theorem exists_maximumIndependentOn_sparse_complement_counts
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) :
    ∃ I : Finset V, IsMaximumIndependentOn G S I ∧
      ((S \ I).card).choose 2 - countIndependent G (S \ I) 2 ≤
        I.card - (S \ I).card - 1 := by
  obtain ⟨I, hI, hbound⟩ := exists_maximumIndependentOn_sparse_complement G hG S
  exact ⟨I, hI, by simpa only [edgeCountOn_eq_choose_sub_countIndependent] using hbound⟩

/-- The same selected subset also satisfies the intrinsic forest bound on Y,
so the minimum of both capacities is available to later structural rows. -/
theorem IsEdgeMinimalMaximumOn.edgeCountOn_complement_le_min
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsEdgeMinimalMaximumOn G S I) (hG : G.IsAcyclic) :
    edgeCountOn G (S \ I) ≤ min (I.card - (S \ I).card - 1) ((S \ I).card - 1) := by
  apply le_min (hI.edgeCountOn_complement_le hG)
  by_cases hY : (S \ I).Nonempty
  · have h := edgeCountOn_add_one_le_card_of_nonempty hG hY
    omega
  · have hY0 : S \ I = ∅ := not_nonempty_iff_eq_empty.mp hY
    rw [hY0, edgeCountOn_eq_choose_sub_countIndependent]
    simp

#print axioms exists_edgeMinimalMaximumOn
#print axioms IsEdgeMinimalMaximumOn.crossingBlock_card_lt_of_boundary
#print axioms exists_maximumIndependentOn_with_positive_boundary_blocks
#print axioms IsEdgeMinimalMaximumOn.card_boundaryCrossingComponents_le
#print axioms edgeCountOn_complement_le_boundaryCrossingComponents_sub_one
#print axioms exists_maximumIndependentOn_sparse_complement
#print axioms exists_maximumIndependentOn_sparse_complement_counts
#print axioms IsEdgeMinimalMaximumOn.edgeCountOn_complement_le_min

end ForestUnimodality
