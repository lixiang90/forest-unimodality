import ForestUnimodality.MaximumIndependent
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.Hall.Finite

/-!
Saturation of the complement of any fixed maximum independent subset.
Maximum cardinality gives Hall's inequality for independent outside sets.
A two-coloring splits an arbitrary outside set into two such sets with
disjoint neighborhoods, proving the full Hall condition. The finite marriage
theorem then gives the injection. Acyclic graphs inherit a two-coloring.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- Neighbors of the vertices in `A`, restricted to `I`. -/
noncomputable def neighborsIn (G : SimpleGraph V) (I A : Finset V) : Finset V := by
  classical
  exact I.filter fun i => ∃ a ∈ A, G.Adj a i

omit [DecidableEq V] in
@[simp] theorem mem_neighborsIn {G : SimpleGraph V} {I A : Finset V} {i : V} :
    i ∈ neighborsIn G I A ↔ i ∈ I ∧ ∃ a ∈ A, G.Adj a i := by
  classical
  simp [neighborsIn]

/-- Maximal cardinality supplies Hall's inequality for an independent outside set. -/
theorem IsMaximumIndependentOn.card_le_neighborsIn_of_indep
    {G : SimpleGraph V} {S I A : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hA : A ∈ independentSubsets G (S \ I)) :
    A.card ≤ (neighborsIn G I A).card := by
  classical
  have hcomplement : neighborsIn G I A = I \ available G I A := by
    ext i
    simp only [mem_neighborsIn, mem_sdiff, mem_available]
    constructor
    · rintro ⟨hi, a, ha, hadj⟩
      exact ⟨hi, fun h => h.2 a ha hadj.symm⟩
    · rintro ⟨hi, h⟩
      have hex : ∃ a ∈ A, G.Adj a i := by
        by_contra hn
        apply h
        refine ⟨hi, ?_⟩
        intro a ha hadj
        exact hn ⟨a, ha, hadj.symm⟩
      exact ⟨hi, hex⟩
  rw [hcomplement, card_sdiff_of_subset (available_subset G I A)]
  have hbound := hI.card_add_available_le hA
  omega

/-- In a two-colored graph the Hall inequalities also hold for outside sets
that need not themselves be independent. -/
theorem IsMaximumIndependentOn.card_le_neighborsIn_of_twoColor
    {G : SimpleGraph V} {S I A : Finset V} (hI : IsMaximumIndependentOn G S I)
    (c : V → Fin 2) (hc : ∀ {v w}, G.Adj v w → c v ≠ c w)
    (hA : A ⊆ S \ I) : A.card ≤ (neighborsIn G I A).card := by
  classical
  let A0 := A.filter fun v => c v = 0
  let A1 := A.filter fun v => c v ≠ 0
  have hi0 : A0 ∈ independentSubsets G (S \ I) := by
    apply mem_independentSubsets.mpr
    refine ⟨(filter_subset _ _).trans hA, ?_⟩
    intro v hv w hw _ hadj
    have hv0 := (mem_filter.mp hv).2
    have hw0 := (mem_filter.mp hw).2
    exact hc hadj (hv0.trans hw0.symm)
  have hi1 : A1 ∈ independentSubsets G (S \ I) := by
    apply mem_independentSubsets.mpr
    refine ⟨(filter_subset _ _).trans hA, ?_⟩
    intro v hv w hw _ hadj
    have hv1 := (mem_filter.mp hv).2
    have hw1 := (mem_filter.mp hw).2
    have hne := hc hadj
    omega
  have hdis : Disjoint (neighborsIn G I A0) (neighborsIn G I A1) := by
    apply disjoint_left.mpr
    intro i hi0 hi1
    obtain ⟨_, a, ha, hai⟩ := mem_neighborsIn.mp hi0
    obtain ⟨_, b, hb, hbi⟩ := mem_neighborsIn.mp hi1
    have ha0 := (mem_filter.mp ha).2
    have hb1 := (mem_filter.mp hb).2
    have hna := hc hai
    have hnb := hc hbi
    omega
  have hsub : neighborsIn G I A0 ∪ neighborsIn G I A1 ⊆ neighborsIn G I A := by
    intro i hi
    rcases mem_union.mp hi with hi | hi
    · obtain ⟨hI', a, ha, hai⟩ := mem_neighborsIn.mp hi
      exact mem_neighborsIn.mpr ⟨hI', a, (mem_filter.mp ha).1, hai⟩
    · obtain ⟨hI', a, ha, hai⟩ := mem_neighborsIn.mp hi
      exact mem_neighborsIn.mpr ⟨hI', a, (mem_filter.mp ha).1, hai⟩
  calc
    A.card = A0.card + A1.card := by
      exact (card_filter_add_card_filter_not (s := A) (p := fun v => c v = 0)).symm
    _ ≤ (neighborsIn G I A0).card + (neighborsIn G I A1).card :=
      Nat.add_le_add (hI.card_le_neighborsIn_of_indep hi0)
        (hI.card_le_neighborsIn_of_indep hi1)
    _ = (neighborsIn G I A0 ∪ neighborsIn G I A1).card :=
      (card_union_of_disjoint hdis).symm
    _ ≤ (neighborsIn G I A).card := card_le_card hsub

/-- A two-coloring and maximum independent subset give a matching that
saturates the complement, expressed as an adjacency-preserving injection. -/
theorem IsMaximumIndependentOn.exists_injective_adj_of_twoColor
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (c : V → Fin 2) (hc : ∀ {v w}, G.Adj v w → c v ≠ c w) :
    ∃ f : (↑(S \ I) : Set V) → (↑I : Set V),
      Function.Injective f ∧ ∀ y, G.Adj y.val (f y).val := by
  classical
  let t : (↑(S \ I) : Set V) → Finset V := fun y => I.filter fun i => G.Adj y.val i
  have hhall : ∀ B : Finset (↑(S \ I) : Set V), B.card ≤ (B.biUnion t).card := by
    intro B
    have hsub : B.image Subtype.val ⊆ S \ I := by
      intro a ha
      obtain ⟨y, _, rfl⟩ := mem_image.mp ha
      exact y.property
    have hbound := hI.card_le_neighborsIn_of_twoColor c hc hsub
    rw [card_image_of_injective _ Subtype.val_injective] at hbound
    have heq : neighborsIn G I (B.image Subtype.val) = B.biUnion t := by
      ext i
      constructor
      · intro hi
        obtain ⟨hiI, a, ha, hai⟩ := mem_neighborsIn.mp hi
        obtain ⟨y, hy, rfl⟩ := mem_image.mp ha
        exact mem_biUnion.mpr ⟨y, hy, mem_filter.mpr ⟨hiI, hai⟩⟩
      · intro hi
        obtain ⟨y, hy, hiy⟩ := mem_biUnion.mp hi
        obtain ⟨hiI, hyi⟩ := mem_filter.mp hiy
        exact mem_neighborsIn.mpr ⟨hiI, y.val, mem_image.mpr ⟨y, hy, rfl⟩, hyi⟩
    simpa only [heq] using hbound
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  refine ⟨fun y => ⟨f y, (mem_filter.mp (hf y)).1⟩, ?_, ?_⟩
  · intro y z hyz
    apply hfinj
    exact congrArg Subtype.val hyz
  · intro y
    exact (mem_filter.mp (hf y)).2

/-- Every maximum independent subset of a bipartite graph admits a matching
from all other vertices of the finite ambient set into that subset. -/
theorem IsMaximumIndependentOn.exists_injective_adj_of_isBipartite
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsBipartite) :
    ∃ f : (↑(S \ I) : Set V) → (↑I : Set V),
      Function.Injective f ∧ ∀ y, G.Adj y.val (f y).val := by
  obtain ⟨c, hc⟩ := hG
  exact hI.exists_injective_adj_of_twoColor c hc

/-- The requested forest saturation theorem, with the maximum independent
subset fixed in advance. Isolated vertices and empty ambient sets are included. -/
theorem IsMaximumIndependentOn.exists_injective_adj_of_isAcyclic
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) :
    ∃ f : (↑(S \ I) : Set V) → (↑I : Set V),
      Function.Injective f ∧ ∀ y, G.Adj y.val (f y).val := by
  exact hI.exists_injective_adj_of_isBipartite hG.isBipartite

#print axioms IsMaximumIndependentOn.card_le_neighborsIn_of_indep
#print axioms IsMaximumIndependentOn.card_le_neighborsIn_of_twoColor
#print axioms IsMaximumIndependentOn.exists_injective_adj_of_twoColor
#print axioms IsMaximumIndependentOn.exists_injective_adj_of_isBipartite
#print axioms IsMaximumIndependentOn.exists_injective_adj_of_isAcyclic

end ForestUnimodality
