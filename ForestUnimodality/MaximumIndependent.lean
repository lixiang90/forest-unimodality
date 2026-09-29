import ForestUnimodality.LayerCounts
import Mathlib.Data.Finset.Max

/-!
Maximum independent subsets and the triangular support of the layer counts.
The size inequality is derived by adjoining all currently available vertices
of I to the outside independent set J; it is not assumed as a counting axiom.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- I has maximum cardinality among independent subsets of the finite set S. -/
def IsMaximumIndependentOn (G : SimpleGraph V) (S I : Finset V) : Prop :=
  I ∈ independentSubsets G S ∧
    ∀ K ∈ independentSubsets G S, K.card ≤ I.card

/-- Every finite ambient set admits a maximum independent subset, including
the empty ambient set. -/
theorem exists_maximumIndependentOn (G : SimpleGraph V) (S : Finset V) :
    ∃ I : Finset V, IsMaximumIndependentOn G S I := by
  classical
  have hempty : (∅ : Finset V) ∈ independentSubsets G S := by
    simp [mem_independentSubsets, SimpleGraph.IsIndepSet, Set.Pairwise]
  have hnonempty : (independentSubsets G S).Nonempty := ⟨∅, hempty⟩
  have hcardNonempty : ((independentSubsets G S).image Finset.card).Nonempty :=
    hnonempty.image Finset.card
  obtain ⟨I, hI, hcard⟩ := mem_image.mp
    (((independentSubsets G S).image Finset.card).max'_mem hcardNonempty)
  refine ⟨I, hI, ?_⟩
  intro K hK
  rw [hcard]
  exact Finset.le_max' _ _ (mem_image_of_mem Finset.card hK)

theorem IsMaximumIndependentOn.subset {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) : I ⊆ S :=
  (mem_independentSubsets.mp hI.1).1

theorem IsMaximumIndependentOn.independent {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) : G.IsIndepSet (I : Set V) :=
  (mem_independentSubsets.mp hI.1).2

/-- The outside independent set and its available vertices in I are disjoint. -/
theorem disjoint_available_of_mem_independentSubsets_sdiff
    {G : SimpleGraph V} {S I J : Finset V}
    (hJ : J ∈ independentSubsets G (S \ I)) :
    Disjoint J (available G I J) := by
  apply disjoint_left.mpr
  intro v hvJ hvA
  exact (mem_sdiff.mp ((mem_independentSubsets.mp hJ).1 hvJ)).2
    ((available_subset G I J) hvA)

/-- A maximum independent subset forces the two layer indices to fit in its
cardinality. This supplies the triangular support used in finite certificates. -/
theorem IsMaximumIndependentOn.card_add_available_le
    {G : SimpleGraph V} {S I J : Finset V}
    (hI : IsMaximumIndependentOn G S I)
    (hJ : J ∈ independentSubsets G (S \ I)) :
    J.card + (available G I J).card ≤ I.card := by
  have hjoin : J ∪ available G I J ∈ independentSubsets G S :=
    join_mem hI.subset hI.independent hJ (Subset.refl _)
  have hbound := hI.2 _ hjoin
  rw [card_union_of_disjoint
    (disjoint_available_of_mem_independentSubsets_sdiff hJ)] at hbound
  exact hbound

/-- Layers beyond j+m=|I| contain no outside independent set. -/
theorem IsMaximumIndependentOn.layerCount_eq_zero_of_card_lt
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) {j m : ℕ}
    (hlarge : I.card < j + m) :
    layerCount G I (S \ I) j m = 0 := by
  classical
  unfold layerCount
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro J hJ
  obtain ⟨hind, hj, hm⟩ := mem_filter.mp hJ
  have hbound := hI.card_add_available_le hind
  rw [hj, hm] at hbound
  exact (not_lt_of_ge hbound) hlarge

#print axioms exists_maximumIndependentOn
#print axioms IsMaximumIndependentOn.card_add_available_le
#print axioms IsMaximumIndependentOn.layerCount_eq_zero_of_card_lt

end ForestUnimodality
