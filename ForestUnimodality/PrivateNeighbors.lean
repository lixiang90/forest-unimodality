import ForestUnimodality.MaximumIndependent

/-!
Private neighbors and the vertices released by deleting one member of an
outside set. These are finite-set identities for arbitrary simple graphs;
no forest hypothesis or counting inequality is assumed.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- Neighbors of u in I which have no other neighbor in J. -/
noncomputable def privateNeighbors (G : SimpleGraph V) (I J : Finset V) (u : V) :
    Finset V := by
  classical
  exact I.filter fun x => G.Adj u x ∧ ∀ v ∈ J, G.Adj v x → v = u

@[simp] theorem mem_privateNeighbors
    {G : SimpleGraph V} {I J : Finset V} {u x : V} :
    x ∈ privateNeighbors G I J u ↔
      x ∈ I ∧ G.Adj u x ∧ ∀ v ∈ J, G.Adj v x → v = u := by
  classical
  simp [privateNeighbors]

theorem privateNeighbors_subset (G : SimpleGraph V) (I J : Finset V) (u : V) :
    privateNeighbors G I J u ⊆ I := by
  intro x hx
  exact (mem_privateNeighbors.mp hx).1

/-- A private neighbor is blocked before its owner is removed. -/
theorem disjoint_available_privateNeighbors
    (G : SimpleGraph V) (I J : Finset V) {u : V} (hu : u ∈ J) :
    Disjoint (available G I J) (privateNeighbors G I J u) := by
  apply disjoint_left.mpr
  intro x hxA hxP
  exact (mem_available.mp hxA).2 u hu (mem_privateNeighbors.mp hxP).2.1.symm

/-- Different members of J cannot share a private neighbor. -/
theorem disjoint_privateNeighbors
    (G : SimpleGraph V) (I J : Finset V) {u v : V}
    (_hu : u ∈ J) (hv : v ∈ J) (huv : u ≠ v) :
    Disjoint (privateNeighbors G I J u) (privateNeighbors G I J v) := by
  apply disjoint_left.mpr
  intro x hxU hxV
  have hvu := (mem_privateNeighbors.mp hxU).2.2 v hv
    (mem_privateNeighbors.mp hxV).2.1
  exact huv hvu.symm

/-- Deleting u releases exactly its private neighbors, in addition to vertices
which were already available. -/
theorem available_erase_eq_union_privateNeighbors
    (G : SimpleGraph V) (I J : Finset V) {u : V} (_hu : u ∈ J) :
    available G I (J.erase u) =
      available G I J ∪ privateNeighbors G I J u := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hxI, hxFree⟩ := mem_available.mp hx
    by_cases hux : G.Adj u x
    · apply mem_union_right
      apply mem_privateNeighbors.mpr
      refine ⟨hxI, hux, ?_⟩
      intro v hv hvx
      by_contra hvu
      exact hxFree v (mem_erase.mpr ⟨hvu, hv⟩) hvx.symm
    · apply mem_union_left
      apply mem_available.mpr
      refine ⟨hxI, ?_⟩
      intro v hv hxv
      by_cases hvu : v = u
      · subst v
        exact hux hxv.symm
      · exact hxFree v (mem_erase.mpr ⟨hvu, hv⟩) hxv
  · intro hx
    rcases mem_union.mp hx with hxA | hxP
    · obtain ⟨hxI, hxFree⟩ := mem_available.mp hxA
      exact mem_available.mpr ⟨hxI, fun v hv => hxFree v (mem_of_mem_erase hv)⟩
    · obtain ⟨hxI, _, hxUnique⟩ := mem_privateNeighbors.mp hxP
      apply mem_available.mpr
      refine ⟨hxI, ?_⟩
      intro v hv hxv
      exact (mem_erase.mp hv).1 (hxUnique v (mem_of_mem_erase hv) hxv.symm)

/-- The exact release-count formula m(J-u)=m(J)+p_u. -/
theorem card_available_erase_eq_add_privateNeighbors
    (G : SimpleGraph V) (I J : Finset V) {u : V} (hu : u ∈ J) :
    (available G I (J.erase u)).card =
      (available G I J).card + (privateNeighbors G I J u).card := by
  rw [available_erase_eq_union_privateNeighbors G I J hu,
    card_union_of_disjoint (disjoint_available_privateNeighbors G I J hu)]

theorem card_privateNeighbors_eq_sub
    (G : SimpleGraph V) (I J : Finset V) {u : V} (hu : u ∈ J) :
    (privateNeighbors G I J u).card =
      (available G I (J.erase u)).card - (available G I J).card := by
  have h := card_available_erase_eq_add_privateNeighbors G I J hu
  omega

/-- Every vertex outside a maximum independent set has a neighbor in it. -/
theorem IsMaximumIndependentOn.exists_adj_of_mem_sdiff
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    {u : V} (hu : u ∈ S \ I) : ∃ x ∈ I, G.Adj u x := by
  classical
  by_contra hnone
  push Not at hnone
  have hJ : ({u} : Finset V) ∈ independentSubsets G (S \ I) := by
    apply mem_independentSubsets.mpr
    exact ⟨singleton_subset_iff.mpr hu, by
      simp [SimpleGraph.IsIndepSet, Set.Pairwise]⟩
  have hAvail : available G I {u} = I := by
    ext x
    constructor
    · exact fun hx => (mem_available.mp hx).1
    · intro hx
      apply mem_available.mpr
      refine ⟨hx, ?_⟩
      intro v hv hxv
      have hvu : v = u := mem_singleton.mp hv
      subst v
      exact hnone x hx hxv.symm
  have hbound := hI.card_add_available_le hJ
  rw [hAvail, card_singleton] at hbound
  omega

#print axioms available_erase_eq_union_privateNeighbors
#print axioms card_available_erase_eq_add_privateNeighbors
#print axioms card_privateNeighbors_eq_sub
#print axioms disjoint_privateNeighbors
#print axioms IsMaximumIndependentOn.exists_adj_of_mem_sdiff

end ForestUnimodality
