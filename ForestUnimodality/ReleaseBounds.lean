import ForestUnimodality.PrivateNeighborBound

/-! The complete feasible range of the private-neighbor release vector. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

/-- Distinct private-neighbor sets are disjoint subsets of the covered part of I. -/
theorem sum_privateNeighbors_card_le_covered (G : SimpleGraph V) (I J : Finset V) :
    (∑ u ∈ J, (privateNeighbors G I J u).card) ≤
      I.card - (available G I J).card := by
  classical
  have hdis : (J : Set V).Pairwise
      (fun u v => Disjoint (privateNeighbors G I J u) (privateNeighbors G I J v)) := by
    intro u hu v hv huv
    exact disjoint_privateNeighbors G I J hu hv huv
  have hsub : J.biUnion (privateNeighbors G I J) ⊆ I \ available G I J := by
    intro x hx
    obtain ⟨u, hu, hxP⟩ := mem_biUnion.mp hx
    apply mem_sdiff.mpr
    refine ⟨(mem_privateNeighbors.mp hxP).1, ?_⟩
    intro hxA
    exact disjoint_left.mp (disjoint_available_privateNeighbors G I J hu) hxA hxP
  calc
    (∑ u ∈ J, (privateNeighbors G I J u).card) =
        (J.biUnion (privateNeighbors G I J)).card := (card_biUnion hdis).symm
    _ ≤ (I \ available G I J).card := card_le_card hsub
    _ = I.card - (available G I J).card :=
      card_sdiff_of_subset (available_subset G I J)

/-- After one deletion, maximal cardinality bounds the released vertices. -/
theorem IsMaximumIndependentOn.privateNeighbors_card_le_release_cap
    {G : SimpleGraph V} {S I J : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hJ : J ∈ independentSubsets G (S \ I)) {u : V} (hu : u ∈ J) :
    (privateNeighbors G I J u).card ≤
      I.card - (available G I J).card - J.card + 1 := by
  have hJerase : J.erase u ∈ independentSubsets G (S \ I) := by
    obtain ⟨hJS, hJI⟩ := mem_independentSubsets.mp hJ
    exact mem_independentSubsets.mpr ⟨(erase_subset u J).trans hJS,
      hJI.mono (Finset.coe_subset.mpr (erase_subset u J))⟩
  have hbound := hI.card_add_available_le hJerase
  have hsupport := hI.card_add_available_le hJ
  rw [card_available_erase_eq_add_privateNeighbors G I J hu] at hbound
  have hcard := card_erase_add_one hu
  omega

/-- The forest lower release budget, expressed without a signed subtraction. -/
theorem IsMaximumIndependentOn.release_cap_le_sum_privateNeighbors
    {G : SimpleGraph V} {S I J : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (hJ : J ∈ independentSubsets G (S \ I)) (hne : J.Nonempty) :
    I.card - (available G I J).card - J.card + 1 ≤
      ∑ u ∈ J, (privateNeighbors G I J u).card := by
  have hdis : Disjoint I J := by
    apply disjoint_left.mpr
    intro u huI huJ
    exact (mem_sdiff.mp ((mem_independentSubsets.mp hJ).1 huJ)).2 huI
  have hbound := covered_card_le_card_sub_one_add_privateNeighbors G hG I J
    hI.independent (mem_independentSubsets.mp hJ).2 hdis hne
  have hsupport := hI.card_add_available_le hJ
  have hpos := card_pos.mpr hne
  omega

#print axioms sum_privateNeighbors_card_le_covered
#print axioms IsMaximumIndependentOn.privateNeighbors_card_le_release_cap
#print axioms IsMaximumIndependentOn.release_cap_le_sum_privateNeighbors
end ForestUnimodality
