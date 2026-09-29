import ForestUnimodality.HardCoreActivityWindow
import ForestUnimodality.PrivateNeighbors

/-! The first genuine pruning step in the adjusted-mean induction. An actual
leaf omitted by a maximum independent set has a positive local remainder.
The adjusted potential of the two smaller graphs remains an induction input. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

/-- Adjusted potential with the actual maximum cardinality supplied separately. -/
noncomputable def adjustedMeanPotential (G : SimpleGraph V) (S : Finset V) (a : ℕ) : ℝ :=
  3 * hardCoreMean G S 2 - (a : ℝ) - (29 / 60 : ℝ) * S.card

/-- First-moment counterpart of the exact vertex-deletion recurrence. -/
theorem hardCore_first_moment_delete_vertex (G : SimpleGraph V) (S : Finset V)
    {v : V} (hv : v ∈ S) (z : ℝ) :
    hardCoreMomentNumerator G S 1 z = hardCoreMomentNumerator G (S.erase v) 1 z +
      z * (hardCoreMomentNumerator G (S \ closedNeighborhoodIn G S v) 1 z +
        partitionFunction G (S \ closedNeighborhoodIn G S v) z) := by
  classical
  unfold hardCoreMomentNumerator partitionFunction
  simp only [pow_one]
  rw [sum_independentSubsets_delete_vertex G S hv]
  congr 1
  rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro J hJ
  rw [card_insert_of_notMem (not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hJ),
    Nat.cast_add, Nat.cast_one, pow_succ]
  ring

/-- An omitted leaf has its unique neighbor inside every chosen maximum set
that omits the leaf. The unique-neighbor hypothesis is relative to S. -/
theorem IsMaximumIndependentOn.neighbor_mem_of_leaf_excluded
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    {l v : V} (hl : l ∈ S) (hlI : l ∉ I)
    (hleaf : ∀ w ∈ S, G.Adj l w → w = v) : v ∈ I ∧ G.Adj l v := by
  obtain ⟨w, hwI, hlw⟩ := hI.exists_adj_of_mem_sdiff (mem_sdiff.mpr ⟨hl, hlI⟩)
  have hwv := hleaf w (hI.subset hwI) hlw
  subst w
  exact ⟨hwI, hlw⟩

theorem sdiff_closedNeighborhoodIn_of_unique_neighbor
    (G : SimpleGraph V) (S : Finset V) {l v : V} (hlv : G.Adj l v)
    (hleaf : ∀ w ∈ S, G.Adj l w → w = v) :
    S \ closedNeighborhoodIn G S l = (S.erase l).erase v := by
  ext w
  simp only [mem_sdiff_closedNeighborhoodIn, mem_erase]
  constructor
  · rintro ⟨hwS, hwl, hn⟩
    refine ⟨?_, hwl, hwS⟩
    intro hwv
    exact hn (hwv ▸ hlv)
  · rintro ⟨hwv, hwl, hwS⟩
    exact ⟨hwS, hwl, fun hlw => hwv (hleaf w hwS hlw)⟩

theorem IsMaximumIndependentOn.erase_ambient_of_not_mem
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    {l : V} (hlI : l ∉ I) : IsMaximumIndependentOn G (S.erase l) I := by
  refine ⟨mem_independentSubsets.mpr ⟨?_, hI.independent⟩, ?_⟩
  · intro w hw
    exact mem_erase.mpr ⟨fun hwl => hlI (hwl ▸ hw), hI.subset hw⟩
  · intro K hK
    exact hI.2 K (independentSubsets_mono G (erase_subset _ _) hK)

/-- The leaf-exclusion state forces the exact one-unit independence-number
drop on deleting its neighbor, with both cardinalities witnessed by maxima. -/
theorem IsMaximumIndependentOn.leaf_exclusion_card_eq
    {G : SimpleGraph V} {S I K : Finset V} (hI : IsMaximumIndependentOn G S I)
    {l v : V} (hl : l ∈ S) (hlI : l ∉ I)
    (hleaf : ∀ w ∈ S, G.Adj l w → w = v)
    (hK : IsMaximumIndependentOn G ((S.erase l).erase v) K) : I.card = K.card + 1 := by
  have hv := hI.neighbor_mem_of_leaf_excluded hl hlI hleaf
  have hclosed := sdiff_closedNeighborhoodIn_of_unique_neighbor G S hv.2 hleaf
  have hKI : K ∈ independentSubsets G (S \ closedNeighborhoodIn G S l) := by
    rw [hclosed]
    exact hK.1
  have hlarge := hI.2 (insert l K)
    (insert_mem_independentSubsets_of_sdiff_closedNeighborhoodIn hl hKI)
  rw [card_insert_of_notMem (not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hKI)] at hlarge
  have hIerase : I.erase v ∈ independentSubsets G ((S.erase l).erase v) := by
    apply mem_independentSubsets.mpr
    refine ⟨?_, hI.independent.mono (coe_subset.mpr (erase_subset _ _))⟩
    intro w hw
    obtain ⟨hwv, hwI⟩ := mem_erase.mp hw
    exact mem_erase.mpr ⟨hwv,
      mem_erase.mpr ⟨fun hwl => hlI (hwl ▸ hwI), hI.subset hwI⟩⟩
  have hsmall := hK.2 (I.erase v) hIerase
  have herase := card_erase_add_one hv.1
  omega

/-- The exact adjusted-potential identity behind leaf pruning. Its two
potential parameters are justified by the actual maximum-cardinality lemma. -/
theorem adjustedMean_leaf_identity
    {G : SimpleGraph V} {S I K : Finset V} (hI : IsMaximumIndependentOn G S I)
    {l v : V} (hl : l ∈ S) (hlI : l ∉ I)
    (hleaf : ∀ w ∈ S, G.Adj l w → w = v)
    (hK : IsMaximumIndependentOn G ((S.erase l).erase v) K) :
    60 * partitionFunction G S (2 : ℝ) * adjustedMeanPotential G S I.card =
      60 * partitionFunction G (S.erase l) (2 : ℝ) *
        adjustedMeanPotential G (S.erase l) I.card +
      120 * partitionFunction G ((S.erase l).erase v) (2 : ℝ) *
        adjustedMeanPotential G ((S.erase l).erase v) K.card +
      124 * partitionFunction G ((S.erase l).erase v) (2 : ℝ) -
        29 * partitionFunction G (S.erase l) (2 : ℝ) := by
  have hv := hI.neighbor_mem_of_leaf_excluded hl hlI hleaf
  have hvH : v ∈ S.erase l := mem_erase.mpr ⟨hv.2.ne.symm, hI.subset hv.1⟩
  have hclosed := sdiff_closedNeighborhoodIn_of_unique_neighbor G S hv.2 hleaf
  have hZ := partitionFunction_delete_vertex G S hl (2 : ℝ)
  have hM := hardCore_first_moment_delete_vertex G S hl (2 : ℝ)
  rw [hclosed] at hZ hM
  have hcardH := card_erase_add_one hl
  have hcardJ := card_erase_add_one hvH
  have hab := hI.leaf_exclusion_card_eq hl hlI hleaf hK
  have hnS : S.card = ((S.erase l).erase v).card + 2 := by omega
  have hnH : (S.erase l).card = ((S.erase l).erase v).card + 1 := by omega
  have hZH := ne_of_gt (partitionFunction_pos G (S.erase l) (by norm_num : (0 : ℝ) ≤ 2))
  have hZJ := ne_of_gt (partitionFunction_pos G ((S.erase l).erase v) (by norm_num : (0 : ℝ) ≤ 2))
  have hZF := ne_of_gt (partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 2))
  unfold adjustedMeanPotential hardCoreMean
  rw [hZ, hM, hnS, hnH, hab]
  have hden : partitionFunction G (S.erase l) (2 : ℝ) +
      2 * partitionFunction G ((S.erase l).erase v) (2 : ℝ) ≠ 0 := by rw [← hZ]; exact hZF
  push_cast
  field_simp
  ring

/-- Actual leaf pruning: if the two smaller graphs satisfy M, an omitted leaf
forces strictly positive adjusted potential in the full graph. -/
theorem adjustedMean_pos_of_leaf_excluded
    {G : SimpleGraph V} {S I K : Finset V} (hI : IsMaximumIndependentOn G S I)
    {l v : V} (hl : l ∈ S) (hlI : l ∉ I)
    (hleaf : ∀ w ∈ S, G.Adj l w → w = v)
    (hK : IsMaximumIndependentOn G ((S.erase l).erase v) K)
    (hH : 0 ≤ adjustedMeanPotential G (S.erase l) I.card)
    (hJ : 0 ≤ adjustedMeanPotential G ((S.erase l).erase v) K.card) :
    0 < adjustedMeanPotential G S I.card := by
  have hv := hI.neighbor_mem_of_leaf_excluded hl hlI hleaf
  have hvH : v ∈ S.erase l := mem_erase.mpr ⟨hv.2.ne.symm, hI.subset hv.1⟩
  have hA := partitionFunction_pos G (S.erase l) (by norm_num : (0 : ℝ) ≤ 2)
  have hB := partitionFunction_pos G ((S.erase l).erase v) (by norm_num : (0 : ℝ) ≤ 2)
  have hF := partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 2)
  have hratio := (partitionFunction_delete_ratio_bounds G (S.erase l) hvH
    (by norm_num : (0 : ℝ) ≤ 2)).2
  have hAB : partitionFunction G (S.erase l) (2 : ℝ) ≤
      3 * partitionFunction G ((S.erase l).erase v) (2 : ℝ) := by
    apply (div_le_iff₀ hB).mp
    simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using hratio
  have hid := adjustedMean_leaf_identity hI hl hlI hleaf hK
  have hprod : 0 < 60 * partitionFunction G S (2 : ℝ) * adjustedMeanPotential G S I.card := by
    nlinarith [mul_nonneg hA.le hH, mul_nonneg hB.le hJ]
  exact pos_of_mul_pos_right hprod (by positivity)

/-- In the induction context of a smallest nonpositive counterexample, every
leaf belongs to the chosen maximum set. Since the maximum set is arbitrary,
this yields the source's assertion about every maximum independent set. -/
theorem IsMaximumIndependentOn.leaf_mem_of_adjustedMean_nonpos
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hbad : adjustedMeanPotential G S I.card ≤ 0)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G T K → 0 ≤ adjustedMeanPotential G T K.card)
    {l v : V} (hl : l ∈ S) (hleaf : ∀ w ∈ S, G.Adj l w → w = v) : l ∈ I := by
  by_contra hlI
  obtain ⟨K, hK⟩ := exists_maximumIndependentOn G ((S.erase l).erase v)
  have hHmax := hI.erase_ambient_of_not_mem hlI
  have hHlt : (S.erase l).card < S.card := by
    have hcard := card_erase_add_one hl
    omega
  have hJlt : ((S.erase l).erase v).card < S.card :=
    (card_le_card (erase_subset v (S.erase l))).trans_lt hHlt
  have hH := hsmaller (S.erase l) (erase_subset l S) hHlt I hHmax
  have hJ := hsmaller ((S.erase l).erase v)
    ((erase_subset v (S.erase l)).trans (erase_subset l S)) hJlt K hK
  have hpos := adjustedMean_pos_of_leaf_excluded hI hl hlI hleaf hK hH hJ
  exact (not_lt_of_ge hbad) hpos

#print axioms hardCore_first_moment_delete_vertex
#print axioms IsMaximumIndependentOn.neighbor_mem_of_leaf_excluded
#print axioms IsMaximumIndependentOn.leaf_exclusion_card_eq
#print axioms adjustedMean_leaf_identity
#print axioms adjustedMean_pos_of_leaf_excluded
#print axioms IsMaximumIndependentOn.leaf_mem_of_adjustedMean_nonpos
end ForestUnimodality
