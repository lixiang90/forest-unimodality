import ForestUnimodality.HardCoreMoments
import ForestUnimodality.GraphRecursion
import ForestUnimodality.GraphBounds
import Mathlib.Topology.Order.IntermediateValue

/-! Actual activity-window ingredients. The lower-activity mean bound follows
from vertex deletion and weighted incidence counting, not from an assumed
endpoint estimate. The high-activity structural lower bound is separate. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

/-- Every bracketed mean has one and only one activity in a positive interval. -/
theorem existsUnique_activity_of_mean_bracket (G : SimpleGraph V) (S : Finset V)
    (hS : S.Nonempty) {lo hi k : ℝ} (hlo : 0 < lo) (horder : lo < hi)
    (hkl : hardCoreMean G S lo ≤ k) (hkh : k ≤ hardCoreMean G S hi) :
    ∃! z : ℝ, z ∈ Set.Icc lo hi ∧ hardCoreMean G S z = k := by
  have hcontinuous : ContinuousOn (hardCoreMean G S) (Set.Icc lo hi) := by
    intro z hz
    exact (hasDerivAt_hardCoreMean G S (hlo.trans_le hz.1)).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hzk⟩ := intermediate_value_Icc horder.le hcontinuous ⟨hkl, hkh⟩
  refine ⟨z, ⟨hz, hzk⟩, ?_⟩
  intro y hy
  exact (hardCoreMean_strictMonoOn G S hS).injOn
    (hlo.trans_le hy.1.1) (hlo.trans_le hz.1) (hy.2.trans hzk.symm)

/-- Partition functions are monotone under enlarging the ambient vertex set
at every nonnegative activity. -/
theorem partitionFunction_mono_set (G : SimpleGraph V) {S T : Finset V}
    (hST : S ⊆ T) {z : ℝ} (hz : 0 ≤ z) :
    partitionFunction G S z ≤ partitionFunction G T z := by
  apply sum_le_sum_of_subset_of_nonneg (independentSubsets_mono G hST)
  intro J _ _
  exact pow_nonneg hz _

/-- Exact weighted family of independent sets containing a specified vertex. -/
theorem sum_independent_containing_vertex (G : SimpleGraph V) (S : Finset V)
    {v : V} (hv : v ∈ S) (z : ℝ) :
    (∑ J ∈ (independentSubsets G S).filter (fun J => v ∈ J), z^J.card) =
      z * partitionFunction G (S \ closedNeighborhoodIn G S v) z := by
  classical
  have hfamily : (independentSubsets G S).filter (fun J => v ∈ J) =
      (independentSubsets G (S \ closedNeighborhoodIn G S v)).image (insert v) := by
    ext J
    constructor
    · intro hJ
      obtain ⟨hJind, hvJ⟩ := mem_filter.mp hJ
      exact mem_image.mpr ⟨J.erase v,
        erase_mem_independentSubsets_sdiff_closedNeighborhoodIn hJind hvJ, insert_erase hvJ⟩
    · intro hJ
      obtain ⟨K, hK, rfl⟩ := mem_image.mp hJ
      exact mem_filter.mpr ⟨insert_mem_independentSubsets_of_sdiff_closedNeighborhoodIn hv hK,
        mem_insert_self _ _⟩
  rw [hfamily, sum_image (insert_injOn_independentSubsets_sdiff_closedNeighborhoodIn G S v)]
  unfold partitionFunction
  rw [mul_sum]
  apply sum_congr rfl
  intro J hJ
  rw [card_insert_of_notMem (not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hJ),
    pow_succ, mul_comm]

/-- Incidence counting identifies the first moment with the sum of occupied
vertex weights. This identity does not need acyclicity. -/
theorem hardCore_first_moment_eq_sum_vertices (G : SimpleGraph V) (S : Finset V) (z : ℝ) :
    hardCoreMomentNumerator G S 1 z =
      ∑ v ∈ S, z * partitionFunction G (S \ closedNeighborhoodIn G S v) z := by
  classical
  have hweights (J : Finset V) (hJ : J ∈ independentSubsets G S) :
      (J.card : ℝ) * z^J.card = ∑ v ∈ S, if v ∈ J then z^J.card else 0 := by
    have hfilter : S.filter (· ∈ J) = J := by
      ext v
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hv => (mem_independentSubsets.mp hJ).1 hv)
    rw [← sum_filter, hfilter]
    simp
  calc
    _ = ∑ J ∈ independentSubsets G S, ∑ v ∈ S, if v ∈ J then z^J.card else 0 := by
      unfold hardCoreMomentNumerator
      simp only [pow_one]
      exact sum_congr rfl hweights
    _ = ∑ v ∈ S, ∑ J ∈ independentSubsets G S, if v ∈ J then z^J.card else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro v hv
      rw [← sum_filter, sum_independent_containing_vertex G S hv z]

/-- The occupied weight at any one vertex is at most λ/(1+λ) of Z,
stated without division. -/
theorem vertex_weight_mul_one_add_le (G : SimpleGraph V) (S : Finset V)
    {v : V} (hv : v ∈ S) {z : ℝ} (hz : 0 ≤ z) :
    (1 + z) * (z * partitionFunction G (S \ closedNeighborhoodIn G S v) z) ≤
      z * partitionFunction G S z := by
  have hsub : S \ closedNeighborhoodIn G S v ⊆ S.erase v := by
    intro w hw
    obtain ⟨hwS, hwne, _⟩ := mem_sdiff_closedNeighborhoodIn.mp hw
    exact mem_erase.mpr ⟨hwne, hwS⟩
  have hmono := partitionFunction_mono_set G hsub hz
  rw [partitionFunction_delete_vertex G S hv z]
  nlinarith [mul_le_mul_of_nonneg_left hmono hz]

/-- The true hard-core mean obeys the universal vertex-marginal upper bound. -/
theorem hardCoreMean_le_card_mul_activity (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : 0 ≤ z) :
    hardCoreMean G S z ≤ (S.card : ℝ) * z / (1 + z) := by
  have hsum := sum_le_sum (fun v hv => vertex_weight_mul_one_add_le G S hv hz)
  have hmoment : (1 + z) * hardCoreMomentNumerator G S 1 z ≤
      (S.card : ℝ) * z * partitionFunction G S z := by
    rw [hardCore_first_moment_eq_sum_vertices]
    simpa only [← mul_sum, sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm] using hsum
  unfold hardCoreMean
  apply (div_le_div_iff₀ (partitionFunction_pos G S hz) (by linarith : 0 < 1 + z)).mpr
  nlinarith

/-- The exact lower-activity endpoint used in the source's integer-rank window. -/
theorem hardCoreMean_one_third_le (G : SimpleGraph V) (S : Finset V) :
    hardCoreMean G S (1 / 3) ≤ (S.card : ℝ) / 4 := by
  have h := hardCoreMean_le_card_mul_activity G S (z := 1 / 3) (by norm_num)
  convert h using 1
  ring

theorem hardCoreMean_one_half_le (G : SimpleGraph V) (S : Finset V) :
    hardCoreMean G S (1 / 2) ≤ (S.card : ℝ) / 3 := by
  have h := hardCoreMean_le_card_mul_activity G S (z := 1 / 2) (by norm_num)
  convert h using 1
  ring

theorem hardCoreMean_one_le (G : SimpleGraph V) (S : Finset V) :
    hardCoreMean G S 1 ≤ (S.card : ℝ) / 2 := by
  simpa only [mul_one, show (1 : ℝ) + 1 = 2 by norm_num] using
    hardCoreMean_le_card_mul_activity G S (z := 1) (by norm_num)

theorem hardCoreMean_two_le (G : SimpleGraph V) (S : Finset V) :
    hardCoreMean G S 2 ≤ 2 * (S.card : ℝ) / 3 := by
  have h := hardCoreMean_le_card_mul_activity G S (z := 2) (by norm_num)
  convert h using 1
  ring

/-- A true deletion-ratio bound, including the [1,3] input used by activity-two
tree-message and host-attachment arguments. -/
theorem partitionFunction_delete_ratio_bounds (G : SimpleGraph V) (S : Finset V)
    {v : V} (hv : v ∈ S) {z : ℝ} (hz : 0 ≤ z) :
    1 ≤ partitionFunction G S z / partitionFunction G (S.erase v) z ∧
      partitionFunction G S z / partitionFunction G (S.erase v) z ≤ 1 + z := by
  have hA := partitionFunction_pos G (S.erase v) hz
  have hB := partitionFunction_pos G (S \ closedNeighborhoodIn G S v) hz
  have hsub : S \ closedNeighborhoodIn G S v ⊆ S.erase v := by
    intro w hw
    obtain ⟨hwS, hwne, _⟩ := mem_sdiff_closedNeighborhoodIn.mp hw
    exact mem_erase.mpr ⟨hwne, hwS⟩
  have hmono := partitionFunction_mono_set G hsub hz
  constructor
  · apply (le_div_iff₀ hA).mpr
    rw [partitionFunction_delete_vertex G S hv z]
    nlinarith
  · apply (div_le_iff₀ hA).mpr
    rw [partitionFunction_delete_vertex G S hv z]
    nlinarith [mul_le_mul_of_nonneg_left hmono hz]

#print axioms existsUnique_activity_of_mean_bracket
#print axioms partitionFunction_mono_set
#print axioms sum_independent_containing_vertex
#print axioms hardCore_first_moment_eq_sum_vertices
#print axioms hardCoreMean_le_card_mul_activity
#print axioms hardCoreMean_one_third_le
#print axioms hardCoreMean_one_half_le
#print axioms partitionFunction_delete_ratio_bounds
end ForestUnimodality
