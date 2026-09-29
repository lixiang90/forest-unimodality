import ForestUnimodality.PrivateNeighbors
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Structural counting bounds used for the private-neighbor inequality. -/

namespace ForestUnimodality

open Finset SimpleGraph
open scoped BigOperators

/-- A nonempty finite forest has at most one fewer edge than vertices. -/
theorem forest_card_edges_add_one_le
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    G.edgeFinset.card + 1 ≤ Fintype.card V := by
  classical
  have hconn : (⊤ : SimpleGraph V).Connected := connected_top
  obtain ⟨T, hGT, _, hT⟩ :=
    hconn.exists_isTree_le_of_le_of_isAcyclic (show G ≤ ⊤ from le_top) hG
  calc
    G.edgeFinset.card + 1 ≤ T.edgeFinset.card + 1 :=
      Nat.add_le_add_right (card_le_card (edgeFinset_mono hGT)) 1
    _ = Fintype.card V := hT.card_edgeFinset

/-- In a finite bipartite forest, if every right vertex has a neighbor, the
right side is bounded by the left side minus one plus its degree-one vertices. -/
theorem bipartite_forest_right_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (A B : Finset V) (hA : A.Nonempty)
    (hAB : G.IsBipartiteWith A B) (hcover : A ∪ B = univ)
    (hpos : ∀ x ∈ B, 0 < G.degree x) :
    B.card ≤ A.card - 1 + (B.filter fun x => G.degree x = 1).card := by
  classical
  letI : Nonempty V := ⟨hA.choose⟩
  have he := forest_card_edges_add_one_le G hG
  have hsum := isBipartiteWith_sum_degrees_eq_card_edges' hAB
  have hcard : A.card + B.card = Fintype.card V := by
    rw [← card_union_of_disjoint (disjoint_coe.mp hAB.disjoint), hcover, card_univ]
  have hpoint : ∀ x ∈ B, 2 ≤ G.degree x + if G.degree x = 1 then 1 else 0 := by
    intro x hx
    have hp := hpos x hx
    split_ifs <;> omega
  have htwo := sum_le_sum hpoint
  have htwo' : 2 * B.card ≤ G.edgeFinset.card +
      (B.filter fun x => G.degree x = 1).card := by
    simpa [sum_add_distrib, hsum, sum_boole, Nat.mul_comm] using htwo
  have hapos := card_pos.mpr hA
  omega

#print axioms forest_card_edges_add_one_le
#print axioms bipartite_forest_right_card_le

/-- The covered I-vertices are bounded by |J|-1 plus the total number of
private neighbors. Neither I nor J is required to be maximum. -/
theorem covered_card_le_card_sub_one_add_privateNeighbors
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (I J : Finset V) (hI : G.IsIndepSet (I : Set V))
    (hJ : G.IsIndepSet (J : Set V)) (hIJ : Disjoint I J) (hne : J.Nonempty) :
    I.card - (available G I J).card ≤
      J.card - 1 + ∑ u ∈ J, (privateNeighbors G I J u).card := by
  classical
  let C := I \ available G I J
  let K := J ∪ C
  let H := G.induce (↑K : Set V)
  let A : Finset K := J.subtype (· ∈ K)
  let B : Finset K := C.subtype (· ∈ K)
  have hJC : Disjoint J C := by
    apply Finset.disjoint_left.mpr
    intro x hxJ hxC
    exact Finset.disjoint_left.mp hIJ (mem_sdiff.mp hxC).1 hxJ
  have hcardA : A.card = J.card := by
    change (J.subtype (· ∈ K)).card = J.card
    rw [card_subtype, filter_eq_self.mpr (subset_union_left : J ⊆ K)]
  have hcardB : B.card = C.card := by
    change (C.subtype (· ∈ K)).card = C.card
    rw [card_subtype, filter_eq_self.mpr (subset_union_right : C ⊆ K)]
  have hA : A.Nonempty := by
    rw [← card_pos, hcardA]
    exact card_pos.mpr hne
  have hcover : A ∪ B = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true, A, B, mem_subtype]
    exact mem_union.mp x.property
  have hAB : H.IsBipartiteWith A B := by
    constructor
    · apply Set.disjoint_left.mpr
      intro x hxA hxB
      exact Finset.disjoint_left.mp hJC (mem_subtype.mp hxA) (mem_subtype.mp hxB)
    · intro x y hxy
      have hxy' : G.Adj x.val y.val := hxy
      have hcolors : (x.val ∈ J ∧ y.val ∈ C) ∨ (x.val ∈ C ∧ y.val ∈ J) := by
        rcases mem_union.mp x.property with hxJ | hxC <;>
          rcases mem_union.mp y.property with hyJ | hyC
        · exact False.elim (hJ hxJ hyJ hxy'.ne hxy')
        · exact Or.inl ⟨hxJ, hyC⟩
        · exact Or.inr ⟨hxC, hyJ⟩
        · exact False.elim
            (hI (mem_sdiff.mp hxC).1 (mem_sdiff.mp hyC).1 hxy'.ne hxy')
      simpa only [A, B, mem_subtype, mem_coe] using hcolors
  have hpos : ∀ x ∈ B, 0 < H.degree x := by
    intro x hxB
    have hxC : x.val ∈ C := mem_subtype.mp hxB
    obtain ⟨hxI, hxNot⟩ := mem_sdiff.mp hxC
    have hex : ∃ u ∈ J, G.Adj x.val u := by
      by_contra hnone
      push Not at hnone
      exact hxNot (mem_available.mpr ⟨hxI, hnone⟩)
    obtain ⟨u, hu, hxu⟩ := hex
    have hxu' : H.Adj x ⟨u, mem_union_left C hu⟩ := hxu
    exact hxu'.degree_pos_left
  have hbound := bipartite_forest_right_card_le H (hG.induce (↑K : Set V))
    A B hA hAB hcover hpos
  let R := B.filter fun x => H.degree x = 1
  have hRimage : R.image Subtype.val ⊆ J.biUnion (privateNeighbors G I J) := by
    intro x hx
    obtain ⟨y, hyR, rfl⟩ := mem_image.mp hx
    obtain ⟨hyB, hydeg⟩ := mem_filter.mp hyR
    have hyC : y.val ∈ C := mem_subtype.mp hyB
    obtain ⟨u, hyu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hydeg
    have huA : u ∈ A := hAB.mem_of_mem_adj' hyB hyu.symm
    have huJ : u.val ∈ J := mem_subtype.mp huA
    apply mem_biUnion.mpr
    refine ⟨u.val, huJ, mem_privateNeighbors.mpr ⟨(mem_sdiff.mp hyC).1,
      hyu.symm, ?_⟩⟩
    intro w hw hwy
    have hyw : H.Adj y ⟨w, mem_union_left C hw⟩ := hwy.symm
    exact congrArg Subtype.val (huniq ⟨w, mem_union_left C hw⟩ hyw)
  have hRcard : R.card ≤ ∑ u ∈ J, (privateNeighbors G I J u).card := by
    calc
      R.card = (R.image Subtype.val).card :=
        (card_image_of_injective R Subtype.val_injective).symm
      _ ≤ (J.biUnion (privateNeighbors G I J)).card := card_le_card hRimage
      _ ≤ ∑ u ∈ J, (privateNeighbors G I J u).card := card_biUnion_le
  have hcounts := card_sdiff_add_card_eq_card (available_subset G I J)
  change C.card + (available G I J).card = I.card at hcounts
  change B.card ≤ A.card - 1 + R.card at hbound
  rw [hcardA, hcardB] at hbound
  omega

#print axioms covered_card_le_card_sub_one_add_privateNeighbors

end ForestUnimodality
