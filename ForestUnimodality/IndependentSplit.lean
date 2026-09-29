import ForestUnimodality.GraphCore
import ForestUnimodality.SubsetPolynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Tauto

/-! An actual bijection behind the forest manuscript's layer decomposition.
The decomposition holds for any independent I in any finite graph: first choose
an independent subset J of the complement, then an arbitrary subset of I
having no neighbors in J. No counting identity is assumed. -/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem split_left_mem {S I K : Finset V} (hK : K ∈ independentSubsets G S) :
    K \ I ∈ independentSubsets G (S \ I) := by
  obtain ⟨hKS, hind⟩ := mem_independentSubsets.mp hK
  apply mem_independentSubsets.mpr
  constructor
  · intro v hv
    obtain ⟨hvK, hvI⟩ := mem_sdiff.mp hv
    exact mem_sdiff.mpr ⟨hKS hvK, hvI⟩
  · apply hind.mono
    exact_mod_cast (sdiff_subset : K \ I ⊆ K)

theorem split_right_subset {S I K : Finset V} (hK : K ∈ independentSubsets G S) :
    K ∩ I ⊆ available G I (K \ I) := by
  obtain ⟨_, hind⟩ := mem_independentSubsets.mp hK
  intro v hv
  obtain ⟨hvK, hvI⟩ := mem_inter.mp hv
  apply mem_available.mpr
  refine ⟨hvI, ?_⟩
  intro w hw
  obtain ⟨hwK, hwI⟩ := mem_sdiff.mp hw
  exact hind hvK hwK (by intro h; exact hwI (h ▸ hvI))

theorem join_mem {S I J T : Finset V}
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    (hJ : J ∈ independentSubsets G (S \ I))
    (hT : T ⊆ available G I J) :
    J ∪ T ∈ independentSubsets G S := by
  obtain ⟨hJS, hindJ⟩ := mem_independentSubsets.mp hJ
  have hTI : T ⊆ I := hT.trans (available_subset _ _ _)
  apply mem_independentSubsets.mpr
  refine ⟨union_subset (hJS.trans sdiff_subset) (hTI.trans hIS), ?_⟩
  intro v hv w hw hne hadj
  rcases mem_union.mp hv with hv | hv <;> rcases mem_union.mp hw with hw | hw
  · exact hindJ hv hw hne hadj
  · exact (mem_available.mp (hT hw)).2 v hv hadj.symm
  · exact (mem_available.mp (hT hv)).2 w hw hadj
  · exact hI (hTI hv) (hTI hw) hne hadj

theorem join_sdiff {S I J T : Finset V}
    (hJ : J ∈ independentSubsets G (S \ I)) (hT : T ⊆ available G I J) :
    (J ∪ T) \ I = J := by
  have hJS := (mem_independentSubsets.mp hJ).1
  have hTI := hT.trans (available_subset _ _ _)
  ext v
  simp only [mem_sdiff, mem_union]
  constructor
  · rintro ⟨hv | hv, hnI⟩
    · exact hv
    · exact (hnI (hTI hv)).elim
  · intro hv
    exact ⟨Or.inl hv, (mem_sdiff.mp (hJS hv)).2⟩

theorem join_inter {S I J T : Finset V}
    (hJ : J ∈ independentSubsets G (S \ I)) (hT : T ⊆ available G I J) :
    (J ∪ T) ∩ I = T := by
  have hJS := (mem_independentSubsets.mp hJ).1
  have hTI := hT.trans (available_subset _ _ _)
  ext v
  simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨hv | hv, hvI⟩
    · exact ((mem_sdiff.mp (hJS hv)).2 hvI).elim
    · exact hv
  · intro hv
    exact ⟨Or.inr hv, hTI hv⟩

theorem split_union (K I : Finset V) : (K \ I) ∪ (K ∩ I) = K := by
  ext v
  simp only [mem_union, mem_sdiff, mem_inter]
  tauto

theorem split_card (K I : Finset V) : K.card = (K \ I).card + (K ∩ I).card := by
  have hd : Disjoint (K \ I) (K ∩ I) := by
    apply disjoint_left.mpr
    intro v hv1 hv2
    exact (mem_sdiff.mp hv1).2 (mem_inter.mp hv2).2
  rw [← card_union_of_disjoint hd, split_union]

/-- The full, ungrouped generating-function decomposition. -/
theorem partitionFunction_split {R : Type*} [CommSemiring R]
    (S I : Finset V) (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) (z : R) :
    partitionFunction G S z =
      ∑ J ∈ independentSubsets G (S \ I),
        ∑ T ∈ (available G I J).powerset, z^(J.card + T.card) := by
  classical
  unfold partitionFunction
  rw [sum_sigma']
  apply sum_bij' (fun K _ => (⟨K \ I, K ∩ I⟩ : (J : Finset V) × Finset V))
    (fun p _ => p.1 ∪ p.2)
  · intro K hK
    exact mem_sigma.mpr ⟨split_left_mem hK, mem_powerset.mpr (split_right_subset hK)⟩
  · intro p hp
    obtain ⟨hJ, hT⟩ := mem_sigma.mp hp
    exact join_mem hIS hI hJ (mem_powerset.mp hT)
  · intro K _
    exact split_union K I
  · intro p hp
    obtain ⟨hJ, hT⟩ := mem_sigma.mp hp
    have hT' := mem_powerset.mp hT
    have h1 := join_sdiff hJ hT'
    have h2 := join_inter hJ hT'
    exact Sigma.ext h1 (heq_of_eq h2)
  · intro K _
    congr 1
    exact split_card K I

#print axioms partitionFunction_split

/-- The manuscript's generating-function decomposition before grouping by
the size and number of available vertices of J. -/
theorem partitionFunction_decomposition {R : Type*} [CommSemiring R]
    (S I : Finset V) (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) (z : R) :
    partitionFunction G S z =
      ∑ J ∈ independentSubsets G (S \ I), z^J.card * (1+z)^(available G I J).card := by
  rw [partitionFunction_split S I hIS hI z]
  apply sum_congr rfl
  intro J _
  exact sum_powerset_pow_add_card (available G I J) z J.card

#print axioms partitionFunction_decomposition

end ForestUnimodality
