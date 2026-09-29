import ForestUnimodality.CrossEdges
import ForestUnimodality.ForestLeaf

/-! Edge and closed-neighborhood counts for vertex deletion. -/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- Deleting a vertex removes exactly its incident edges within S. -/
theorem edgeCountOn_erase_add_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {v : V} (hv : v ∈ S) :
    edgeCountOn G S = edgeCountOn G (S.erase v) + (S.filter (G.Adj v)).card := by
  classical
  have hd : Disjoint ({v} : Finset V) (S.erase v) := by simp
  have hi : G.IsIndepSet (({v} : Finset V) : Set V) := by
    simp [SimpleGraph.IsIndepSet]
  have hu : ({v} : Finset V) ∪ S.erase v = S := by simp [insert_erase hv]
  have hb := edgeCountOn_union_of_indep G {v} (S.erase v) hd hi
  rw [hu, sum_singleton] at hb
  have hf : (S.erase v).filter (G.Adj v) = S.filter (G.Adj v) := by
    ext w
    simp only [mem_filter, mem_erase]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · exact fun h => ⟨⟨h.2.ne.symm, h.1⟩, h.2⟩
  rwa [hf] at hb

/-- The closed neighborhood is the vertex together with its open neighbors. -/
theorem closedNeighborhoodIn_eq_insert_filter
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {v : V} (hv : v ∈ S) :
    closedNeighborhoodIn G S v = insert v (S.filter (G.Adj v)) := by
  classical
  ext w
  simp only [closedNeighborhoodIn, mem_filter, mem_insert]
  constructor
  · rintro ⟨hw, rfl | hadj⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hw, hadj⟩
  · rintro (rfl | ⟨hw, hadj⟩)
    · exact ⟨hv, Or.inl rfl⟩
    · exact ⟨hw, Or.inr hadj⟩

/-- In a simple graph, closed-neighborhood cardinality is degree plus one. -/
theorem card_closedNeighborhoodIn_eq_degree_add_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {v : V} (hv : v ∈ S) :
    (closedNeighborhoodIn G S v).card = (S.filter (G.Adj v)).card + 1 := by
  rw [closedNeighborhoodIn_eq_insert_filter G S hv, card_insert_of_notMem]
  simp

theorem closedNeighborhoodIn_subset (G : SimpleGraph V) (S : Finset V) (v : V) :
    closedNeighborhoodIn G S v ⊆ S := by
  classical
  exact filter_subset _ _

/-- For an isolated vertex the two deletion branches use the same remainder. -/
theorem sdiff_closedNeighborhoodIn_eq_erase_of_degree_zero
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {v : V} (hv : v ∈ S)
    (hzero : (S.filter (G.Adj v)).card = 0) :
    S \ closedNeighborhoodIn G S v = S.erase v := by
  rw [closedNeighborhoodIn_eq_insert_filter G S hv, card_eq_zero.mp hzero]
  ext w
  simp [and_comm]

/-- Deleting a closed neighborhood gives the exact remaining vertex count. -/
theorem card_sdiff_closedNeighborhoodIn
    (G : SimpleGraph V) (S : Finset V) (v : V) :
    (S \ closedNeighborhoodIn G S v).card = S.card - (closedNeighborhoodIn G S v).card :=
  card_sdiff_of_subset (closedNeighborhoodIn_subset G S v)

#print axioms edgeCountOn_erase_add_degree
#print axioms card_closedNeighborhoodIn_eq_degree_add_one
#print axioms sdiff_closedNeighborhoodIn_eq_erase_of_degree_zero

end ForestUnimodality
