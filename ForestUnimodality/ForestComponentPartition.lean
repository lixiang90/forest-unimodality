import ForestUnimodality.SparseComplementHelpers
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Exact finite component partitions and forest Euler counting. -/
namespace ForestUnimodality.ForestComponentPartition
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V] [Fintype V]
attribute [local instance] Classical.propDecidable

noncomputable def componentVertices (G : SimpleGraph V) (c : G.ConnectedComponent) : Finset V :=
  univ.filter fun x => G.connectedComponentMk x = c

omit [DecidableEq V] in
@[simp] theorem mem_componentVertices (G : SimpleGraph V) (c : G.ConnectedComponent) (x : V) :
    x ∈ componentVertices G c ↔ G.connectedComponentMk x = c := by
  simp [componentVertices]

omit [DecidableEq V] in
theorem coe_componentVertices (G : SimpleGraph V) (c : G.ConnectedComponent) :
    (componentVertices G c : Set V) = c.supp := by
  ext x
  simp [mem_componentVertices, ConnectedComponent.mem_supp_iff]

omit [DecidableEq V] in
theorem componentVertices_disjoint (G : SimpleGraph V) {c d : G.ConnectedComponent}
    (hcd : c ≠ d) : Disjoint (componentVertices G c) (componentVertices G d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hcd (((mem_componentVertices G c x).mp hx).symm.trans
    ((mem_componentVertices G d x).mp hy))

omit [DecidableEq V] in
theorem componentVertices_nonempty (G : SimpleGraph V) (c : G.ConnectedComponent) :
    (componentVertices G c).Nonempty := by
  obtain ⟨x, rfl⟩ := c.exists_rep
  exact ⟨x, (mem_componentVertices G _ _).mpr rfl⟩

theorem componentVertices_cover (G : SimpleGraph V) :
    (univ : Finset G.ConnectedComponent).biUnion (componentVertices G) = univ := by
  ext x
  simp only [mem_biUnion, mem_univ, true_and, iff_true]
  exact ⟨G.connectedComponentMk x, (mem_componentVertices G _ _).mpr rfl⟩

omit [DecidableEq V] in
theorem componentVertices_no_edges (G : SimpleGraph V) {c d : G.ConnectedComponent}
    (hcd : c ≠ d) {x y : V} (hx : x ∈ componentVertices G c)
    (hy : y ∈ componentVertices G d) : ¬ G.Adj x y := by
  intro hxy
  have he := ConnectedComponent.eq.mpr hxy.reachable
  rw [(mem_componentVertices G c x).mp hx, (mem_componentVertices G d y).mp hy] at he
  exact hcd he

omit [DecidableEq V] in
theorem componentVertices_connected (G : SimpleGraph V) (c : G.ConnectedComponent) :
    (G.induce (componentVertices G c : Set V)).Connected := by
  rw [coe_componentVertices]
  exact c.connected_toSimpleGraph

theorem sum_componentVertices_card (G : SimpleGraph V) :
    (∑ c : G.ConnectedComponent, (componentVertices G c).card) = Fintype.card V := by
  classical
  have h := sum_fiberwise_of_maps_to
    (show ∀ x ∈ (univ : Finset V), G.connectedComponentMk x ∈
      (univ : Finset G.ConnectedComponent) from fun _ _ => mem_univ _) (fun _ => (1 : ℕ))
  simpa [componentVertices] using h

theorem component_tree_card (G : SimpleGraph V) (hG : G.IsAcyclic)
    (c : G.ConnectedComponent) : edgeCountOn G (componentVertices G c) + 1 =
      (componentVertices G c).card := by
  classical
  have hc : (G.induce (componentVertices G c : Set V)).IsTree := by
    rw [coe_componentVertices]
    exact ⟨c.connected_toSimpleGraph, hG.induce c.supp⟩
  have h := hc.card_edgeFinset
  rw [← edgeCountOn_eq_card_edgeFinset_induce] at h
  exact h.trans (Fintype.card_coe (componentVertices G c))

theorem sum_component_edgeCount (G : SimpleGraph V) :
    (∑ c : G.ConnectedComponent, edgeCountOn G (componentVertices G c)) =
      edgeCountOn G (univ : Finset V) := by
  classical
  let es := fun c : G.ConnectedComponent => edgePairsOn G (componentVertices G c)
  have hd : (↑(univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).PairwiseDisjoint es := by
    intro c _ d _ hcd
    apply Finset.disjoint_left.mpr
    intro E hEc hEd
    obtain ⟨hsub, hcard, _⟩ := mem_edgePairsOn.mp hEc
    obtain ⟨x, hx⟩ := card_pos.mp (show 0 < E.card by omega)
    exact Finset.disjoint_left.mp (componentVertices_disjoint G hcd)
      (hsub hx) ((mem_edgePairsOn.mp hEd).1 hx)
  have hu : (univ : Finset G.ConnectedComponent).biUnion es = edgePairsOn G univ := by
    ext E
    constructor
    · intro hE
      obtain ⟨c, _, hE⟩ := mem_biUnion.mp hE
      obtain ⟨_, hc, hi⟩ := mem_edgePairsOn.mp hE
      exact mem_edgePairsOn.mpr ⟨subset_univ _, hc, hi⟩
    · intro hE
      obtain ⟨x, _, y, _, hxy, rfl⟩ := edgePairsOn_exists_adj_pair hE
      apply mem_biUnion.mpr
      refine ⟨G.connectedComponentMk x, mem_univ _, mem_edgePairsOn.mpr ⟨?_, ?_, ?_⟩⟩
      · apply insert_subset
        · exact (mem_componentVertices G _ _).mpr rfl
        · apply singleton_subset_iff.mpr
          apply (mem_componentVertices G _ _).mpr
          exact (ConnectedComponent.eq.mpr hxy.reachable).symm
      · simp [hxy.ne]
      · intro hi
        exact hi (by simp) (by simp) hxy.ne hxy
  have hcard := card_biUnion hd
  rw [hu] at hcard
  exact hcard.symm

/-- Euler's exact edge/component identity for a finite forest, including
the empty graph and singleton components. -/
theorem forest_euler (G : SimpleGraph V) (hG : G.IsAcyclic) :
    edgeCountOn G (univ : Finset V) + Fintype.card G.ConnectedComponent = Fintype.card V := by
  classical
  have h := Finset.sum_congr rfl (fun c (_ : c ∈ (univ : Finset G.ConnectedComponent)) =>
    component_tree_card G hG c)
  simpa only [sum_add_distrib, sum_component_edgeCount, sum_const, card_univ,
    smul_eq_mul, mul_one, sum_componentVertices_card] using h


#print axioms forest_euler
end ForestUnimodality.ForestComponentPartition
