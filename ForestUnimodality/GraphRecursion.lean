import ForestUnimodality.GraphCore

/-!
Vertex-deletion recurrences for independent sets on a finite vertex subset.
The proofs use the partition into sets that omit or contain the chosen vertex.
They are independent of any forest hypothesis or external proof development.
-/

namespace ForestUnimodality

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- The closed neighborhood of v, restricted to the finite ambient set S. -/
noncomputable def closedNeighborhoodIn (G : SimpleGraph V) (S : Finset V) (v : V) :
    Finset V := by
  classical
  exact S.filter fun w => w = v ∨ G.Adj v w

@[simp] theorem mem_sdiff_closedNeighborhoodIn
    {G : SimpleGraph V} {S : Finset V} {v w : V} :
    w ∈ S \ closedNeighborhoodIn G S v ↔
      w ∈ S ∧ w ≠ v ∧ ¬ G.Adj v w := by
  classical
  simp only [closedNeighborhoodIn, mem_sdiff, mem_filter]
  tauto

@[simp] theorem not_mem_sdiff_closedNeighborhoodIn
    (G : SimpleGraph V) (S : Finset V) (v : V) :
    v ∉ S \ closedNeighborhoodIn G S v := by
  rw [mem_sdiff_closedNeighborhoodIn]
  simp

theorem mem_independentSubsets_erase_iff
    {G : SimpleGraph V} {S J : Finset V} {v : V} :
    J ∈ independentSubsets G (S.erase v) ↔
      J ∈ independentSubsets G S ∧ v ∉ J := by
  constructor
  · intro h
    obtain ⟨hsub, hind⟩ := mem_independentSubsets.mp h
    refine ⟨mem_independentSubsets.mpr ⟨hsub.trans (erase_subset _ _), hind⟩, ?_⟩
    intro hv
    exact (mem_erase.mp (hsub hv)).1 rfl
  · rintro ⟨h, hv⟩
    obtain ⟨hsub, hind⟩ := mem_independentSubsets.mp h
    refine mem_independentSubsets.mpr ⟨?_, hind⟩
    intro w hw
    exact mem_erase.mpr ⟨fun h => hv (h ▸ hw), hsub hw⟩

/-- Removing a contained vertex leaves an independent set outside its closed
neighborhood. -/
theorem erase_mem_independentSubsets_sdiff_closedNeighborhoodIn
    {G : SimpleGraph V} {S J : Finset V} {v : V}
    (hJ : J ∈ independentSubsets G S) (hv : v ∈ J) :
    J.erase v ∈ independentSubsets G (S \ closedNeighborhoodIn G S v) := by
  obtain ⟨hsub, hind⟩ := mem_independentSubsets.mp hJ
  refine mem_independentSubsets.mpr ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨hwv, hwJ⟩ := mem_erase.mp hw
    exact mem_sdiff_closedNeighborhoodIn.mpr
      ⟨hsub hwJ, hwv, hind hv hwJ hwv.symm⟩
  · exact hind.mono fun w hw => mem_of_mem_erase hw

/-- Inserting v reverses the deletion on independent subsets outside the
closed neighborhood, provided that v belongs to the ambient set. -/
theorem insert_mem_independentSubsets_of_sdiff_closedNeighborhoodIn
    {G : SimpleGraph V} {S J : Finset V} {v : V} (hv : v ∈ S)
    (hJ : J ∈ independentSubsets G (S \ closedNeighborhoodIn G S v)) :
    insert v J ∈ independentSubsets G S := by
  obtain ⟨hsub, hind⟩ := mem_independentSubsets.mp hJ
  have hdata : ∀ w ∈ J, w ∈ S ∧ w ≠ v ∧ ¬ G.Adj v w :=
    fun w hw => mem_sdiff_closedNeighborhoodIn.mp (hsub hw)
  refine mem_independentSubsets.mpr ⟨?_, ?_⟩
  · intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact hv
    · exact (hdata w hw).1
  · intro a ha b hb hab
    rcases mem_insert.mp ha with hav | haJ
    · subst a
      rcases mem_insert.mp hb with hbv | hbJ
      · subst b
        exact False.elim (hab rfl)
      · exact (hdata b hbJ).2.2
    · rcases mem_insert.mp hb with hbv | hbJ
      · subst b
        exact fun hadj => (hdata a haJ).2.2 hadj.symm
      · exact hind haJ hbJ hab

theorem not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn
    {G : SimpleGraph V} {S J : Finset V} {v : V}
    (hJ : J ∈ independentSubsets G (S \ closedNeighborhoodIn G S v)) :
    v ∉ J := by
  intro hv
  exact not_mem_sdiff_closedNeighborhoodIn G S v ((mem_independentSubsets.mp hJ).1 hv)

/-- Insertion is injective on the independent sets used by the second branch. -/
theorem insert_injOn_independentSubsets_sdiff_closedNeighborhoodIn
    (G : SimpleGraph V) (S : Finset V) (v : V) :
    Set.InjOn (insert v)
      (↑(independentSubsets G (S \ closedNeighborhoodIn G S v)) : Set (Finset V)) := by
  intro J hJ K hK h
  have hvJ := not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hJ
  have hvK := not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hK
  have he := congrArg (fun T : Finset V => T.erase v) h
  simpa [hvJ, hvK] using he

/-- The two branches of the deletion partition are disjoint. -/
theorem independentSubsets_delete_disjoint
    (G : SimpleGraph V) (S : Finset V) (v : V) :
    Disjoint (independentSubsets G (S.erase v))
      ((independentSubsets G (S \ closedNeighborhoodIn G S v)).image (insert v)) := by
  classical
  apply disjoint_left.mpr
  intro J hJ hImage
  obtain ⟨K, _, rfl⟩ := mem_image.mp hImage
  exact (mem_independentSubsets_erase_iff.mp hJ).2 (mem_insert_self _ _)

/-- Exact finite-set decomposition underlying both recurrences. -/
theorem independentSubsets_delete_vertex
    (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v ∈ S) :
    independentSubsets G S = independentSubsets G (S.erase v) ∪
      (independentSubsets G (S \ closedNeighborhoodIn G S v)).image (insert v) := by
  classical
  ext J
  constructor
  · intro hJ
    by_cases hvJ : v ∈ J
    · apply mem_union_right
      exact mem_image.mpr ⟨J.erase v,
        erase_mem_independentSubsets_sdiff_closedNeighborhoodIn hJ hvJ,
        insert_erase hvJ⟩
    · exact mem_union_left _ (mem_independentSubsets_erase_iff.mpr ⟨hJ, hvJ⟩)
  · intro hJ
    rcases mem_union.mp hJ with hJ | hJ
    · exact (mem_independentSubsets_erase_iff.mp hJ).1
    · obtain ⟨K, hK, rfl⟩ := mem_image.mp hJ
      exact insert_mem_independentSubsets_of_sdiff_closedNeighborhoodIn hv hK

/-- The deletion partition transports arbitrary additive weights. -/
theorem sum_independentSubsets_delete_vertex {R : Type*} [AddCommMonoid R]
    (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v ∈ S) (f : Finset V → R) :
    (∑ J ∈ independentSubsets G S, f J) =
      (∑ J ∈ independentSubsets G (S.erase v), f J) +
        ∑ J ∈ independentSubsets G (S \ closedNeighborhoodIn G S v), f (insert v J) := by
  classical
  rw [independentSubsets_delete_vertex G S hv,
    sum_union (independentSubsets_delete_disjoint G S v),
    sum_image (insert_injOn_independentSubsets_sdiff_closedNeighborhoodIn G S v)]

/-- The standard independence generating-function recurrence. -/
theorem partitionFunction_delete_vertex {R : Type*} [CommSemiring R]
    (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v ∈ S) (z : R) :
    partitionFunction G S z = partitionFunction G (S.erase v) z +
      z * partitionFunction G (S \ closedNeighborhoodIn G S v) z := by
  classical
  unfold partitionFunction
  rw [sum_independentSubsets_delete_vertex G S hv, mul_sum]
  congr 1
  apply sum_congr rfl
  intro J hJ
  rw [card_insert_of_notMem
    (not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hJ), pow_succ]
  exact mul_comm _ _

/-- A cardinality count can be expressed as a sum of indicator weights. -/
theorem countIndependent_eq_sum (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    countIndependent G S k =
      ∑ J ∈ independentSubsets G S, if J.card = k then 1 else 0 := by
  classical
  simp [countIndependent]

/-- The coefficient recurrence, with k+1 avoiding truncated subtraction. -/
theorem countIndependent_succ_delete_vertex
    (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v ∈ S) (k : ℕ) :
    countIndependent G S (k + 1) = countIndependent G (S.erase v) (k + 1) +
      countIndependent G (S \ closedNeighborhoodIn G S v) k := by
  classical
  simp only [countIndependent_eq_sum]
  rw [sum_independentSubsets_delete_vertex G S hv]
  congr 1
  apply sum_congr rfl
  intro J hJ
  rw [card_insert_of_notMem
    (not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hJ)]
  simp

#print axioms independentSubsets_delete_vertex
#print axioms partitionFunction_delete_vertex
#print axioms countIndependent_succ_delete_vertex

end ForestUnimodality
