import Mathlib.Combinatorics.SimpleGraph.Acyclic
import ForestUnimodality.GraphRecursion

/-! A finite nonempty forest has a vertex of degree at most one.
The proof extends the forest to a tree on the same vertex type and uses
the existing tree leaf theorem. No connectivity assumption is required. -/

namespace ForestUnimodality

open SimpleGraph

theorem exists_degree_le_one_of_isAcyclic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    ∃ v : V, G.degree v ≤ 1 := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · letI : Subsingleton V := hV
    exact ⟨Classical.arbitrary V, by simp⟩
  · letI : Nontrivial V := hV
    have hconn : (⊤ : SimpleGraph V).Connected := connected_top
    obtain ⟨T, hGT, _, hT⟩ :=
      hconn.exists_isTree_le_of_le_of_isAcyclic (show G ≤ ⊤ from le_top) hG
    obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
    exact ⟨v, (degree_le_of_le hGT).trans_eq hv⟩

#print axioms exists_degree_le_one_of_isAcyclic

/-- The leaf bound on a nonempty finite vertex subset. The ambient vertex type
need not be finite. -/
theorem exists_closedNeighborhoodIn_card_le_two
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, (closedNeighborhoodIn G S v).card ≤ 2 := by
  classical
  let H := G.induce (↑S : Set V)
  letI : Nonempty (↑S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  obtain ⟨v, hv⟩ := exists_degree_le_one_of_isAcyclic H (hG.induce (↑S : Set V))
  refine ⟨v.val, v.property, ?_⟩
  have hsub : closedNeighborhoodIn G S v.val ⊆
      insert v.val ((H.neighborFinset v).image Subtype.val) := by
    intro w hw
    have hw' : w ∈ S ∧ (w = v.val ∨ G.Adj v.val w) := by
      simpa only [closedNeighborhoodIn, Finset.mem_filter] using hw
    rcases hw'.2 with rfl | hadj
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      refine Finset.mem_image.mpr ⟨⟨w, hw'.1⟩, ?_, rfl⟩
      exact (H.mem_neighborFinset v ⟨w, hw'.1⟩).mpr hadj
  calc
    (closedNeighborhoodIn G S v.val).card ≤
        (insert v.val ((H.neighborFinset v).image Subtype.val)).card :=
      Finset.card_le_card hsub
    _ ≤ ((H.neighborFinset v).image Subtype.val).card + 1 := Finset.card_insert_le _ _
    _ ≤ (H.neighborFinset v).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
    _ ≤ 2 := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using Nat.add_le_add_right hv 1

#print axioms exists_closedNeighborhoodIn_card_le_two

end ForestUnimodality
