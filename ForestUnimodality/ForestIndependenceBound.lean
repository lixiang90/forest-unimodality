import ForestUnimodality.ForestLeaf
import ForestUnimodality.MaximumIndependent

/-!
The independence number of a finite forest is at least half its order.
We repeatedly select a vertex whose restricted closed neighborhood has at
most two vertices. Deleting that neighborhood and then inserting the selected
vertex constructs an independent set with the required cardinality bound.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- Every finite vertex subset of an acyclic graph has an independent subset
whose cardinality, doubled, is at least the size of the ambient subset. -/
theorem exists_independentSubsets_card_bound_of_isAcyclic
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) :
    ∃ J ∈ independentSubsets G S, S.card ≤ 2 * J.card := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hS : S.Nonempty
  · obtain ⟨v, hv, hsmall⟩ := exists_closedNeighborhoodIn_card_le_two G hG S hS
    have hnsub : closedNeighborhoodIn G S v ⊆ S := by
      exact filter_subset _ _
    have hnnonempty : (closedNeighborhoodIn G S v).Nonempty := by
      refine ⟨v, ?_⟩
      simp [closedNeighborhoodIn, hv]
    obtain ⟨J, hJ, hcard⟩ := ih (S \ closedNeighborhoodIn G S v)
      (sdiff_ssubset hnsub hnnonempty)
    refine ⟨insert v J,
      insert_mem_independentSubsets_of_sdiff_closedNeighborhoodIn hv hJ, ?_⟩
    have hsum := card_sdiff_add_card_eq_card hnsub
    rw [card_insert_of_notMem
      (not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hJ)]
    omega
  · have hS0 : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    subst S
    refine ⟨∅, ?_, by simp⟩
    simp [mem_independentSubsets, SimpleGraph.IsIndepSet, Set.Pairwise]

/-- Maximum cardinality transfers the forest bound to any chosen maximum
independent subset. No finiteness of the ambient vertex type is required. -/
theorem IsMaximumIndependentOn.card_le_two_mul_of_isAcyclic
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic) :
    S.card ≤ 2 * I.card := by
  obtain ⟨J, hJ, hcard⟩ := exists_independentSubsets_card_bound_of_isAcyclic G hG S
  exact hcard.trans (Nat.mul_le_mul_left 2 (hI.2 J hJ))

#print axioms exists_independentSubsets_card_bound_of_isAcyclic
#print axioms IsMaximumIndependentOn.card_le_two_mul_of_isAcyclic

end ForestUnimodality
