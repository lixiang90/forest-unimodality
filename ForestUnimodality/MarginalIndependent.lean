import ForestUnimodality.HardCoreBipartiteVariance
import ForestUnimodality.AdjustedMeanLeaf

/-! Independent sets maximizing actual occupation mass. These are not
maximum-cardinality sets. All comparisons use the same activity and graph. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

def IsMaximumWeightedIndependentOn (G : SimpleGraph V) (S I : Finset V)
    (w : V → ℝ) : Prop :=
  I ∈ independentSubsets G S ∧
    ∀ J ∈ independentSubsets G S, (∑ v ∈ J, w v) ≤ ∑ v ∈ I, w v

theorem exists_maximumWeightedIndependentOn (G : SimpleGraph V) (S : Finset V)
    (w : V → ℝ) : ∃ I, IsMaximumWeightedIndependentOn G S I w := by
  classical
  have he : (∅ : Finset V) ∈ independentSubsets G S := by
    simp [mem_independentSubsets, SimpleGraph.IsIndepSet, Set.Pairwise]
  let f : Finset V → ℝ := fun J => ∑ v ∈ J, w v
  have hne := (show (independentSubsets G S).Nonempty from ⟨∅, he⟩).image f
  obtain ⟨I, hI, hf⟩ := mem_image.mp (((independentSubsets G S).image f).max'_mem hne)
  refine ⟨I, hI, ?_⟩
  intro J hJ
  change f J ≤ f I
  rw [hf]
  exact Finset.le_max' _ _ (mem_image_of_mem f hJ)

theorem IsMaximumWeightedIndependentOn.subset {G : SimpleGraph V} {S I : Finset V}
    {w : V → ℝ} (hI : IsMaximumWeightedIndependentOn G S I w) : I ⊆ S :=
  (mem_independentSubsets.mp hI.1).1

theorem IsMaximumWeightedIndependentOn.independent {G : SimpleGraph V} {S I : Finset V}
    {w : V → ℝ} (hI : IsMaximumWeightedIndependentOn G S I w) : G.IsIndepSet (I : Set V) :=
  (mem_independentSubsets.mp hI.1).2

theorem IsMaximumWeightedIndependentOn.exists_adj_of_excluded
    {G : SimpleGraph V} {S I : Finset V} {w : V → ℝ}
    (hI : IsMaximumWeightedIndependentOn G S I w) {v : V}
    (hv : v ∈ S) (hvi : v ∉ I) (hw : 0 < w v) :
    ∃ u ∈ I, G.Adj v u := by
  classical
  by_contra! hno
  have hJ : I ∈ independentSubsets G (S \ closedNeighborhoodIn G S v) := by
    refine mem_independentSubsets.mpr ⟨?_, hI.independent⟩
    intro u hu
    exact mem_sdiff_closedNeighborhoodIn.mpr ⟨hI.subset hu, fun huv => hvi (huv ▸ hu), hno u hu⟩
  have hb := hI.2 (insert v I) (insert_mem_independentSubsets_of_sdiff_closedNeighborhoodIn hv hJ)
  rw [sum_insert hvi] at hb
  linarith

theorem IsMaximumWeightedIndependentOn.isolated_mem
    {G : SimpleGraph V} {S I : Finset V} {w : V → ℝ}
    (hI : IsMaximumWeightedIndependentOn G S I w) {v : V}
    (hv : v ∈ S) (hw : 0 < w v) (hiso : ∀ u ∈ S, ¬ G.Adj v u) : v ∈ I := by
  by_contra hvi
  obtain ⟨u, hu, hadj⟩ := hI.exists_adj_of_excluded hv hvi hw
  exact hiso u (hI.subset hu) hadj

theorem IsMaximumWeightedIndependentOn.leaf_mem_of_weight_lt
    {G : SimpleGraph V} {S I : Finset V} {w : V → ℝ}
    (hI : IsMaximumWeightedIndependentOn G S I w) {l v : V}
    (hl : l ∈ S) (hw : 0 < w l) (hwv : w v < w l)
    (hleaf : ∀ u ∈ S, G.Adj l u → u = v) : l ∈ I := by
  classical
  by_contra hli
  obtain ⟨u, hu, hadj⟩ := hI.exists_adj_of_excluded hl hli hw
  have huv := hleaf u (hI.subset hu) hadj
  subst u
  have hJ : I.erase v ∈ independentSubsets G (S \ closedNeighborhoodIn G S l) := by
    refine mem_independentSubsets.mpr ⟨?_, hI.independent.mono (coe_subset.mpr (erase_subset _ _))⟩
    intro x hx
    have hxi := mem_of_mem_erase hx
    exact mem_sdiff_closedNeighborhoodIn.mpr ⟨hI.subset hxi,
      fun hxl => hli (hxl ▸ hxi),
      fun hax => (mem_erase.mp hx).1 (hleaf x (hI.subset hxi) hax)⟩
  have hbound := hI.2 (insert l (I.erase v))
    (insert_mem_independentSubsets_of_sdiff_closedNeighborhoodIn hl hJ)
  rw [sum_insert (fun h => hli (mem_of_mem_erase h))] at hbound
  have hsum := sum_erase_add I w hu
  linarith

theorem partitionFunction_lt_of_new_vertex (G : SimpleGraph V) {S T : Finset V}
    (hST : S ⊆ T) {v : V} (hvT : v ∈ T) (hvS : v ∉ S) {z : ℝ} (hz : 0 < z) :
    partitionFunction G S z < partitionFunction G T z := by
  have hsub : S ⊆ T.erase v := by
    intro x hx
    exact mem_erase.mpr ⟨fun hxv => hvS (hxv ▸ hx), hST hx⟩
  have hmono := partitionFunction_mono_set G hsub hz.le
  have hpos := mul_pos hz (partitionFunction_pos G (T \ closedNeighborhoodIn G T v) hz.le)
  rw [partitionFunction_delete_vertex G T hvT z]
  linarith

theorem hardCoreVertexMarginal_eq_delete_ratio (G : SimpleGraph V) (S : Finset V)
    {v : V} (hv : v ∈ S) (z : ℝ) :
    hardCoreVertexMarginal G S z v =
      z * partitionFunction G (S \ closedNeighborhoodIn G S v) z / partitionFunction G S z := by
  rw [hardCoreVertexMarginal, sum_independent_containing_vertex G S hv z]

theorem hardCoreVertexMarginal_pos (G : SimpleGraph V) (S : Finset V)
    {v : V} (hv : v ∈ S) {z : ℝ} (hz : 0 < z) : 0 < hardCoreVertexMarginal G S z v := by
  rw [hardCoreVertexMarginal_eq_delete_ratio G S hv z]
  exact div_pos (mul_pos hz (partitionFunction_pos G _ hz.le)) (partitionFunction_pos G S hz.le)

theorem hardCoreVertexMarginal_le_activity (G : SimpleGraph V) (S : Finset V)
    {v : V} (hv : v ∈ S) {z : ℝ} (hz : 0 < z) :
    hardCoreVertexMarginal G S z v ≤ z / (1 + z) := by
  have hsub : S \ closedNeighborhoodIn G S v ⊆ S.erase v := by
    intro x hx
    obtain ⟨hxS, hxv, _⟩ := mem_sdiff_closedNeighborhoodIn.mp hx
    exact mem_erase.mpr ⟨hxv, hxS⟩
  have hmono := partitionFunction_mono_set G hsub hz.le
  have hrec := partitionFunction_delete_vertex G S hv z
  rw [hardCoreVertexMarginal_eq_delete_ratio G S hv z]
  apply (div_le_div_iff₀ (partitionFunction_pos G S hz.le) (by linarith : 0 < 1 + z)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hmono hz.le]

theorem hardCoreVertexMarginal_lt_activity_of_adj (G : SimpleGraph V) (S : Finset V)
    {v u : V} (hv : v ∈ S) (hu : u ∈ S) (hvu : G.Adj v u) {z : ℝ} (hz : 0 < z) :
    hardCoreVertexMarginal G S z v < z / (1 + z) := by
  have hsub : S \ closedNeighborhoodIn G S v ⊆ S.erase v := by
    intro x hx
    obtain ⟨hxS, hxv, _⟩ := mem_sdiff_closedNeighborhoodIn.mp hx
    exact mem_erase.mpr ⟨hxv, hxS⟩
  have huD : u ∈ S.erase v := mem_erase.mpr ⟨hvu.ne.symm, hu⟩
  have huC : u ∉ S \ closedNeighborhoodIn G S v := by
    intro hx
    exact (mem_sdiff_closedNeighborhoodIn.mp hx).2.2 hvu
  have hlt := partitionFunction_lt_of_new_vertex G hsub huD huC hz
  have hrec := partitionFunction_delete_vertex G S hv z
  rw [hardCoreVertexMarginal_eq_delete_ratio G S hv z]
  apply (div_lt_div_iff₀ (partitionFunction_pos G S hz.le) (by linarith : 0 < 1 + z)).mpr
  nlinarith [mul_lt_mul_of_pos_left hlt hz]

/-- A leaf has strictly larger occupation probability than its neighbor
whenever that neighbor has another neighbor in the ambient graph. -/
theorem hardCoreVertexMarginal_neighbor_lt_leaf (G : SimpleGraph V) (S : Finset V)
    {l v u : V} (hl : l ∈ S) (hv : v ∈ S) (hu : u ∈ S)
    (hlv : G.Adj l v) (hvu : G.Adj v u) (hul : u ≠ l)
    (hleaf : ∀ x ∈ S, G.Adj l x → x = v) {z : ℝ} (hz : 0 < z) :
    hardCoreVertexMarginal G S z v < hardCoreVertexMarginal G S z l := by
  have hsub : S \ closedNeighborhoodIn G S v ⊆ S \ closedNeighborhoodIn G S l := by
    intro x hx
    obtain ⟨hxs, hxv, hvx⟩ := mem_sdiff_closedNeighborhoodIn.mp hx
    exact mem_sdiff_closedNeighborhoodIn.mpr ⟨hxs,
      fun hxl => hvx (hxl ▸ hlv.symm), fun hlx => hxv (hleaf x hxs hlx)⟩
  have humem : u ∈ S \ closedNeighborhoodIn G S l :=
    mem_sdiff_closedNeighborhoodIn.mpr ⟨hu, hul, fun hlu => hvu.ne (hleaf u hu hlu).symm⟩
  have hunot : u ∉ S \ closedNeighborhoodIn G S v := by
    intro h
    exact (mem_sdiff_closedNeighborhoodIn.mp h).2.2 hvu
  have hlt := partitionFunction_lt_of_new_vertex G hsub humem hunot hz
  rw [hardCoreVertexMarginal_eq_delete_ratio G S hv z,
    hardCoreVertexMarginal_eq_delete_ratio G S hl z]
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlt hz) (partitionFunction_pos G S hz.le)

abbrev IsMaximumMarginalIndependentOn (G : SimpleGraph V) (S I : Finset V) (z : ℝ) : Prop :=
  IsMaximumWeightedIndependentOn G S I (hardCoreVertexMarginal G S z)

theorem IsMaximumMarginalIndependentOn.half_mean
    {G : SimpleGraph V} {S I : Finset V} {z : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsBipartite) :
    hardCoreMean G S z / 2 ≤ hardCoreOccupiedMass G S I z := by
  obtain ⟨J, hJS, hJ, hw⟩ := exists_independent_half_occupation_mass_of_isBipartite G hG S z
  exact hw.trans (hI.2 J (mem_independentSubsets.mpr ⟨hJS, hJ⟩))

theorem IsMaximumMarginalIndependentOn.leaf_mem
    {G : SimpleGraph V} {S I : Finset V} {z : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hz : 0 < z)
    {l v u : V} (hl : l ∈ S) (hv : v ∈ S) (hu : u ∈ S)
    (hlv : G.Adj l v) (hvu : G.Adj v u) (hul : u ≠ l)
    (hleaf : ∀ x ∈ S, G.Adj l x → x = v) : l ∈ I :=
  hI.leaf_mem_of_weight_lt hl (hardCoreVertexMarginal_pos G S hl hz)
    (hardCoreVertexMarginal_neighbor_lt_leaf G S hl hv hu hlv hvu hul hleaf hz) hleaf

#print axioms exists_maximumWeightedIndependentOn
#print axioms hardCoreVertexMarginal_neighbor_lt_leaf
#print axioms hardCoreVertexMarginal_lt_activity_of_adj
#print axioms IsMaximumMarginalIndependentOn.half_mean
#print axioms IsMaximumMarginalIndependentOn.leaf_mem
end ForestUnimodality
