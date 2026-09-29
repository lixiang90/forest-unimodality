import ForestUnimodality.MarginalIndependent
import ForestUnimodality.ForestComponentPartition
import ForestUnimodality.ForestMatching
import ForestUnimodality.ForestIndependenceBound
import ForestUnimodality.AdjustedMeanPath

/-! Complement structure for independent sets maximizing actual vertex
marginals. Maximum cardinality is never imposed on that selected set. -/

namespace ForestUnimodality

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- An excluded vertex always has a selected neighbor at positive activity. -/
theorem IsMaximumMarginalIndependentOn.excluded_has_neighbor
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z)
    {x : V} (hx : x ∈ S \ B) : ∃ y ∈ B, G.Adj x y :=
  hB.exists_adj_of_excluded (mem_sdiff.mp hx).1 (mem_sdiff.mp hx).2
    (hardCoreVertexMarginal_pos G S (mem_sdiff.mp hx).1 hz)

/-- If an excluded vertex has exactly one neighbor in the ambient set,
that neighbor also has no other ambient neighbor. Thus this is a two-vertex
component, precisely the leaf exception needed in the counting argument. -/
theorem IsMaximumMarginalIndependentOn.excluded_leaf_neighbor_unique
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z)
    {x y : V} (hx : x ∈ S \ B) (hy : y ∈ S) (hxy : G.Adj x y)
    (hxleaf : ∀ u ∈ S, G.Adj x u → u = y) :
    ∀ u ∈ S, G.Adj y u → u = x := by
  intro u hu hyu
  by_contra hux
  exact (mem_sdiff.mp hx).2
    (hB.leaf_mem hz (mem_sdiff.mp hx).1 hy hu hxy hyu hux hxleaf)

namespace MarginalComplementMatching
open ForestComponentPartition

section FiniteComponents

variable [Fintype V]
attribute [local instance] Classical.propDecidable

omit [DecidableEq V] [Fintype V] in
/-- Vertices reachable from an isolated edge are one of its endpoints. -/
theorem reachable_mem_pair (G : SimpleGraph V) {x y u : V}
    (hx : ∀ w, G.Adj x w → w = y) (hy : ∀ w, G.Adj y w → w = x)
    (hu : G.Reachable x u) : u = x ∨ u = y := by
  have aux {a b : V} (p : G.Walk a b) (ha : a = x ∨ a = y) : b = x ∨ b = y := by
    induction p with
    | nil => exact ha
    | @cons a b c hab p ih =>
      apply ih
      rcases ha with rfl | rfl
      · exact Or.inr (hx b hab)
      · exact Or.inl (hy b hab)
  obtain ⟨p⟩ := hu
  exact aux p (Or.inl rfl)

noncomputable def isolatedVerticesOn (G : SimpleGraph V) (C : Finset V) : Finset V :=
  C.filter fun x => ∀ y ∈ C, ¬ G.Adj x y

noncomputable def excludedLeafExceptions (G : SimpleGraph V) (B : Finset V) : Finset V :=
  (univ \ B).filter fun x => G.degree x = 1

theorem excludedLeafExceptions_card_le_components_of_conditions
    (G : SimpleGraph V) (B : Finset V)
    (hdom : ∀ x ∈ (univ : Finset V) \ B, ∃ y ∈ B, G.Adj x y)
    (hleaf : ∀ x ∈ (univ : Finset V) \ B, ∀ y, G.Adj x y →
      (∀ u, G.Adj x u → u = y) → ∀ u, G.Adj y u → u = x) :
    (excludedLeafExceptions G B).card ≤ Fintype.card G.ConnectedComponent := by
  classical
  have hinj : Set.InjOn G.connectedComponentMk (excludedLeafExceptions G B : Set V) := by
    intro x hx u hu heq
    obtain ⟨hxC, hxdeg⟩ := mem_filter.mp hx
    obtain ⟨huC, _⟩ := mem_filter.mp hu
    obtain ⟨v, hvB, hxv⟩ := hdom x hxC
    obtain ⟨w, hxw, hwuniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hxdeg
    have hxuniq : ∀ a, G.Adj x a → a = v := by
      intro a hxa
      exact (hwuniq a hxa).trans (hwuniq v hxv).symm
    have hvuniq : ∀ a, G.Adj v a → a = x := by
      intro a hva
      exact hleaf x hxC v hxv hxuniq a hva
    have hreach : G.Reachable x u := ConnectedComponent.eq.mp heq
    rcases reachable_mem_pair G hxuniq hvuniq hreach with he | he
    · exact he.symm
    · exact False.elim ((mem_sdiff.mp huC).2 (he ▸ hvB))
  calc
    (excludedLeafExceptions G B).card =
        ((excludedLeafExceptions G B).image G.connectedComponentMk).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (univ : Finset G.ConnectedComponent).card := card_le_card (subset_univ _)
    _ = _ := card_univ

theorem edgeCountOn_univ_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCountOn G (univ : Finset V) = G.edgeFinset.card := by
  classical
  rw [edgeCountOn_eq_card_edgeFinset_induce]
  let e : (G.induce ((univ : Finset V) : Set V)) ≃g G :=
    { toEquiv :=
        { toFun := Subtype.val
          invFun := fun x => ⟨x, mem_univ _⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := by intro x y; rfl }
  exact e.card_edgeFinset_eq

theorem crossing_bipartite (G : SimpleGraph V) (B : Finset V) :
    (crossingGraph G univ B).IsBipartiteWith B ((univ : Finset V) \ B : Finset V) := by
  refine ⟨?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp hy).2 hx)
  · intro x y hxy
    rcases hxy.2.2.2 with h | h
    · exact Or.inl ⟨h.1, mem_sdiff.mpr ⟨mem_univ _, h.2⟩⟩
    · exact Or.inr ⟨mem_sdiff.mpr ⟨mem_univ _, h.2⟩, h.1⟩

theorem crossing_and_internal_edges (G : SimpleGraph V) (B : Finset V)
    (hB : G.IsIndepSet (B : Set V)) :
    edgeCountOn G (univ \ B) + edgeCountOn (crossingGraph G univ B) univ =
      edgeCountOn G univ := by
  classical
  have hdis : Disjoint (edgePairsOn G (univ \ B))
      (edgePairsOn (crossingGraph G univ B) univ) := by
    apply Finset.disjoint_left.mpr
    intro T hT hTx
    obtain ⟨x, _, y, _, hxy, heq⟩ := edgePairsOn_exists_adj_pair hTx
    have hxC := (mem_edgePairsOn.mp hT).1 (heq ▸ (by simp : x ∈ ({x,y} : Finset V)))
    have hyC := (mem_edgePairsOn.mp hT).1 (heq ▸ (by simp : y ∈ ({x,y} : Finset V)))
    rcases hxy.2.2.2 with h | h
    · exact (mem_sdiff.mp hxC).2 h.1
    · exact (mem_sdiff.mp hyC).2 h.1
  have heq : edgePairsOn G (univ \ B) ∪ edgePairsOn (crossingGraph G univ B) univ =
      edgePairsOn G univ := by
    ext T
    constructor
    · intro hT
      rcases mem_union.mp hT with hT | hT
      · obtain ⟨_, hc, hn⟩ := mem_edgePairsOn.mp hT
        exact mem_edgePairsOn.mpr ⟨subset_univ _, hc, hn⟩
      · obtain ⟨x, _, y, _, hxy, rfl⟩ := edgePairsOn_exists_adj_pair hT
        exact mem_edgePairsOn.mpr ⟨subset_univ _, by simp [hxy.1.ne],
          fun hi => hi (by simp) (by simp) hxy.1.ne hxy.1⟩
    · intro hT
      obtain ⟨x, _, y, _, hxy, rfl⟩ := edgePairsOn_exists_adj_pair hT
      by_cases hx : x ∈ B
      · have hy : y ∉ B := fun hy => hB hx hy hxy.ne hxy
        apply mem_union_right
        exact mem_edgePairsOn.mpr ⟨subset_univ _, by simp [hxy.ne], fun hi =>
          hi (by simp) (by simp) hxy.ne ⟨hxy, mem_univ _, mem_univ _, Or.inl ⟨hx, hy⟩⟩⟩
      · by_cases hy : y ∈ B
        · apply mem_union_right
          exact mem_edgePairsOn.mpr ⟨subset_univ _, by simp [hxy.ne], fun hi =>
            hi (by simp) (by simp) hxy.ne ⟨hxy, mem_univ _, mem_univ _, Or.inr ⟨hy, hx⟩⟩⟩
        · apply mem_union_left
          exact mem_edgePairsOn.mpr ⟨insert_subset (mem_sdiff.mpr ⟨mem_univ _, hx⟩)
            (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_univ _, hy⟩)),
            by simp [hxy.ne], fun hi => hi (by simp) (by simp) hxy.ne hxy⟩
  have hc := card_union_of_disjoint hdis
  rw [heq] at hc
  exact hc.symm

theorem crossing_degree_eq_at_isolated {G : SimpleGraph V} {B : Finset V} {x : V}
    (hx : x ∈ isolatedVerticesOn G (univ \ B)) :
    (crossingGraph G univ B).degree x = G.degree x := by
  classical
  apply congrArg Finset.card
  ext y
  simp only [SimpleGraph.mem_neighborFinset]
  constructor
  · exact fun h => h.1
  · intro hxy
    have hxC := (mem_filter.mp hx).1
    have hyB : y ∈ B := by
      by_contra hy
      exact (mem_filter.mp hx).2 y (mem_sdiff.mpr ⟨mem_univ _, hy⟩) hxy
    exact ⟨hxy, mem_univ _, mem_univ _, Or.inr ⟨hyB, (mem_sdiff.mp hxC).2⟩⟩

theorem complement_edges_add_isolates_le_of_conditions
    {G : SimpleGraph V} (hG : G.IsAcyclic) {B : Finset V}
    (hB : G.IsIndepSet (B : Set V))
    (hdom : ∀ x ∈ (univ : Finset V) \ B, ∃ y ∈ B, G.Adj x y)
    (hleaf : ∀ x ∈ (univ : Finset V) \ B, ∀ y, G.Adj x y →
      (∀ u, G.Adj x u → u = y) → ∀ u, G.Adj y u → u = x) :
    edgeCountOn G (univ \ B) + (isolatedVerticesOn G (univ \ B)).card ≤ B.card := by
  classical
  let C := (univ : Finset V) \ B
  let X := crossingGraph G univ B
  let L := excludedLeafExceptions G B
  have hpoint : ∀ x ∈ C, 1 + (if x ∈ isolatedVerticesOn G C then 1 else 0) ≤
      X.degree x + (if x ∈ L then 1 else 0) := by
    intro x hx
    obtain ⟨y, hyB, hxy⟩ := hdom x hx
    have hcross : X.Adj x y :=
      ⟨hxy, mem_univ _, mem_univ _, Or.inr ⟨hyB, (mem_sdiff.mp hx).2⟩⟩
    have hpos := hcross.degree_pos_left
    by_cases hi : x ∈ isolatedVerticesOn G C
    · have heq := crossing_degree_eq_at_isolated hi
      change X.degree x = G.degree x at heq
      by_cases hL : x ∈ L
      · simp only [if_pos hi, if_pos hL]; omega
      · have hn : G.degree x ≠ 1 := by
          intro he
          exact hL (mem_filter.mpr ⟨hx, he⟩)
        simp only [if_pos hi, if_neg hL]
        omega
    · simp only [if_neg hi, add_zero]
      split_ifs <;> omega
  have hs := Finset.sum_le_sum hpoint
  have hI : C.filter (fun x => x ∈ isolatedVerticesOn G C) = isolatedVerticesOn G C := by
    ext x
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun h => (mem_filter.mp h).1
  have hL : C.filter (fun x => x ∈ L) = L := by
    ext x
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun h => (mem_filter.mp h).1
  have hdegree := isBipartiteWith_sum_degrees_eq_card_edges' (crossing_bipartite G B)
  change (∑ x ∈ C, X.degree x) = X.edgeFinset.card at hdegree
  rw [← edgeCountOn_univ_eq X] at hdegree
  have hbound : C.card + (isolatedVerticesOn G C).card ≤
      edgeCountOn X univ + L.card := by
    simpa only [sum_add_distrib, sum_const, sum_boole, hI, hL, smul_eq_mul, mul_one,
      hdegree, Nat.cast_id] using hs
  have htotal := crossing_and_internal_edges G B hB
  have heuler := forest_euler G hG
  have hex := excludedLeafExceptions_card_le_components_of_conditions G B hdom hleaf
  have hcard : C.card + B.card = Fintype.card V := by
    exact (card_sdiff_add_card_eq_card (subset_univ B)).trans card_univ
  change edgeCountOn G C + (isolatedVerticesOn G C).card ≤ B.card
  change edgeCountOn G C + edgeCountOn X univ = edgeCountOn G univ at htotal
  change L.card ≤ Fintype.card G.ConnectedComponent at hex
  omega

/-- A non-isolated independent vertex can be assigned an incident edge,
and two independent vertices cannot receive the same edge. -/
theorem independent_card_le_edges_add_isolates
    (G : SimpleGraph V) {C J : Finset V} (hJ : J ∈ independentSubsets G C) :
    J.card ≤ edgeCountOn G C + (isolatedVerticesOn G C).card := by
  classical
  let D := J \ isolatedVerticesOn G C
  have hex : ∀ x : D, ∃ y ∈ C, G.Adj x.val y := by
    intro x
    have hxJ := (mem_sdiff.mp x.property).1
    have hxC := (mem_independentSubsets.mp hJ).1 hxJ
    have hxnot := (mem_sdiff.mp x.property).2
    by_contra hnone
    push Not at hnone
    exact hxnot (mem_filter.mpr ⟨hxC, hnone⟩)
  choose y hyC hxy using hex
  let f : D → Finset V := fun x => {x.val, y x}
  have hfmem : ∀ x : D, f x ∈ edgePairsOn G C := by
    intro x
    exact mem_edgePairsOn.mpr ⟨insert_subset
      ((mem_independentSubsets.mp hJ).1 (mem_sdiff.mp x.property).1)
      (singleton_subset_iff.mpr (hyC x)), by simp [f, (hxy x).ne],
      fun hi => hi (by simp [f]) (by simp [f]) (hxy x).ne (hxy x)⟩
  have hfinj : Function.Injective f := by
    intro x x' he
    have hx : x.val ∈ f x' := by rw [← he]; simp [f]
    rcases mem_insert.mp hx with hxx | hxy'
    · exact Subtype.ext hxx
    · have hxy' : x.val = y x' := mem_singleton.mp hxy'
      by_cases hxx : x.val = x'.val
      · exact Subtype.ext hxx
      · exact False.elim ((mem_independentSubsets.mp hJ).2
          (mem_sdiff.mp x'.property).1 (mem_sdiff.mp x.property).1 (Ne.symm hxx)
          (hxy' ▸ hxy x'))
  have hD : D.card ≤ edgeCountOn G C := by
    have hc := card_le_card (show (univ.image f) ⊆ edgePairsOn G C from by
      intro E hE
      obtain ⟨x, _, rfl⟩ := mem_image.mp hE
      exact hfmem x)
    simpa only [card_image_of_injective _ hfinj, card_univ, Fintype.card_coe, edgeCountOn] using hc
  have hc := card_sdiff_add_card_inter J (isolatedVerticesOn G C)
  have hi := card_le_card (inter_subset_right : J ∩ isolatedVerticesOn G C ⊆ isolatedVerticesOn G C)
  change D.card + (J ∩ isolatedVerticesOn G C).card = J.card at hc
  omega


end FiniteComponents

/-- The complement of an actual maximum-marginal independent set has no
independent subset larger than the selected set. The ambient vertex set is
an arbitrary finite subset, and the ambient type need not be finite. -/
theorem independent_complement_card_le
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B J : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z)
    (hJ : J ∈ independentSubsets G (S \ B)) : J.card ≤ B.card := by
  classical
  let H := G.induce (S : Set V)
  let B' : Finset S := B.subtype (· ∈ S)
  let J' : Finset S := J.subtype (· ∈ S)
  have hB' : H.IsIndepSet (B' : Set S) := by
    intro x hx y hy hne hxy
    exact hB.independent (mem_subtype.mp hx) (mem_subtype.mp hy)
      (fun he => hne (Subtype.ext he)) hxy
  have hdom : ∀ x ∈ (univ : Finset S) \ B', ∃ y ∈ B', H.Adj x y := by
    intro x hx
    have hxC : x.val ∈ S \ B := mem_sdiff.mpr ⟨x.property,
      fun hxB => (mem_sdiff.mp hx).2 (mem_subtype.mpr hxB)⟩
    obtain ⟨y, hyB, hxy⟩ := hB.excluded_has_neighbor hz hxC
    exact ⟨⟨y, hB.subset hyB⟩, mem_subtype.mpr hyB, hxy⟩
  have hleaf : ∀ x ∈ (univ : Finset S) \ B', ∀ y, H.Adj x y →
      (∀ u, H.Adj x u → u = y) → ∀ u, H.Adj y u → u = x := by
    intro x hx y hxy hxuniq u hyu
    have hxC : x.val ∈ S \ B := mem_sdiff.mpr ⟨x.property,
      fun hxB => (mem_sdiff.mp hx).2 (mem_subtype.mpr hxB)⟩
    apply Subtype.ext
    apply hB.excluded_leaf_neighbor_unique hz hxC y.property hxy
    · intro a ha hxa
      exact congrArg Subtype.val (hxuniq ⟨a, ha⟩ hxa)
    · exact u.property
    · exact hyu
  have hbound := complement_edges_add_isolates_le_of_conditions (hG.induce (S : Set V))
    hB' hdom hleaf
  have hJ' : J' ∈ independentSubsets H (univ \ B') := by
    apply mem_independentSubsets.mpr
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxJ := mem_subtype.mp hx
      have hxC := (mem_independentSubsets.mp hJ).1 hxJ
      exact mem_sdiff.mpr ⟨mem_univ _, fun hxB =>
        (mem_sdiff.mp hxC).2 (mem_subtype.mp hxB)⟩
    · intro x hx y hy hne hxy
      exact (mem_independentSubsets.mp hJ).2 (mem_subtype.mp hx) (mem_subtype.mp hy)
        (fun he => hne (Subtype.ext he)) hxy
  have h := (independent_card_le_edges_add_isolates H hJ').trans hbound
  have hBcard : B'.card = B.card := by
    change (B.subtype (· ∈ S)).card = B.card
    rw [card_subtype, filter_eq_self.mpr hB.subset]
  have hJsub : J ⊆ S := (mem_independentSubsets.mp hJ).1.trans sdiff_subset
  have hJcard : J'.card = J.card := by
    change (J.subtype (· ∈ S)).card = J.card
    rw [card_subtype, filter_eq_self.mpr hJsub]
  simpa only [hBcard, hJcard] using h

/-- A concrete matching represented by disjoint unordered endpoint pairs. -/
structure EdgeMatchingOn (G : SimpleGraph V) (C : Finset V) (M : Finset (Finset V)) : Prop where
  edges : M ⊆ edgePairsOn G C
  disjoint : ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F

theorem exists_complement_matching
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z) :
    ∃ M : Finset (Finset V), EdgeMatchingOn G (S \ B) M ∧
      S.card - 2 * B.card ≤ M.card := by
  classical
  let C := S \ B
  obtain ⟨I, hI⟩ := exists_maximumIndependentOn G C
  have hIcard := independent_complement_card_le hG hB hz hI.1
  obtain ⟨f, hfinj, hfadj⟩ := hI.exists_injective_adj_of_isAcyclic hG
  let D := C \ I
  let pair : (↑D : Set V) → Finset V := fun x => {x.val, (f x).val}
  have hxnot (x : (↑D : Set V)) : x.val ∉ I := (mem_sdiff.mp x.property).2
  have hpairinj : Function.Injective pair := by
    intro x y he
    have hx : x.val ∈ pair y := by rw [← he]; simp [pair]
    rcases mem_insert.mp hx with h | h
    · exact Subtype.ext h
    · exact False.elim (hxnot x ((mem_singleton.mp h) ▸ (f y).property))
  let M := (univ : Finset (↑D : Set V)).image pair
  have hM : EdgeMatchingOn G C M := by
    constructor
    · intro E hE
      obtain ⟨x, _, rfl⟩ := mem_image.mp hE
      exact mem_edgePairsOn.mpr ⟨insert_subset (mem_sdiff.mp x.property).1
        (singleton_subset_iff.mpr (hI.subset (f x).property)),
        by simp [pair, (hfadj x).ne],
        fun hi => hi (by simp [pair]) (by simp [pair]) (hfadj x).ne (hfadj x)⟩
    · intro E hE F hF hEF
      obtain ⟨x, _, rfl⟩ := mem_image.mp hE
      obtain ⟨y, _, rfl⟩ := mem_image.mp hF
      have hxy : x ≠ y := fun he => hEF (congrArg pair he)
      apply Finset.disjoint_left.mpr
      intro v hvx hvy
      simp only [pair, mem_insert, mem_singleton] at hvx hvy
      rcases hvx with hvx | hvx <;> rcases hvy with hvy | hvy
      · exact hxy (Subtype.ext (hvx.symm.trans hvy))
      · exact hxnot x ((hvx.symm.trans hvy) ▸ (f y).property)
      · exact hxnot y ((hvy.symm.trans hvx) ▸ (f x).property)
      · exact hxy (hfinj (Subtype.ext (hvx.symm.trans hvy)))
  have hcard : M.card = D.card := by
    change ((univ : Finset (↑D : Set V)).image pair).card = D.card
    rw [card_image_of_injective _ hpairinj, card_univ]
    exact Fintype.card_coe D
  have hDC : D.card + I.card = C.card := card_sdiff_add_card_eq_card hI.subset
  have hCB : C.card + B.card = S.card := card_sdiff_add_card_eq_card hB.subset
  refine ⟨M, hM, ?_⟩
  rw [hcard]
  omega

theorem exists_complement_matching_exact
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z) :
    ∃ M : Finset (Finset V), EdgeMatchingOn G (S \ B) M ∧
      M.card = S.card - 2 * B.card := by
  obtain ⟨M, hM, hsize⟩ := exists_complement_matching hG hB hz
  obtain ⟨L, hLM, hL⟩ := Finset.exists_subset_card_eq hsize
  exact ⟨L, ⟨hLM.trans hM.edges, fun E hE F hF hEF =>
    hM.disjoint E (hLM hE) F (hLM hF) hEF⟩, hL⟩

theorem order_le_three_mul_selected
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z) :
    S.card ≤ 3 * B.card := by
  obtain ⟨J, hJ, hhalf⟩ := exists_independentSubsets_card_bound_of_isAcyclic G hG (S \ B)
  have hj := independent_complement_card_le hG hB hz hJ
  have hsum := card_sdiff_add_card_eq_card hB.subset
  omega

theorem independent_complement_card_le_half
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B J : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z)
    (hJ : J ∈ independentSubsets G (S \ B)) : 2 * J.card ≤ S.card := by
  have hjB := independent_complement_card_le hG hB hz hJ
  have hjC := card_le_card (mem_independentSubsets.mp hJ).1
  have hsum := card_sdiff_add_card_eq_card hB.subset
  omega

theorem independenceNumber_complement_le_half
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z) :
    independenceNumberOn G (S \ B) ≤ S.card / 2 := by
  obtain ⟨J, hJ⟩ := exists_maximumIndependentOn G (S \ B)
  have hj := independent_complement_card_le_half hG hB hz hJ.1
  rw [hJ.card_eq_independenceNumberOn] at hj
  omega

#print axioms forest_euler
#print axioms IsMaximumMarginalIndependentOn.excluded_leaf_neighbor_unique
#print axioms independent_complement_card_le
#print axioms exists_complement_matching
#print axioms exists_complement_matching_exact
#print axioms order_le_three_mul_selected
#print axioms independenceNumber_complement_le_half

end MarginalComplementMatching
end ForestUnimodality
