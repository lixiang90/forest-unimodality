import ForestUnimodality.UnitActivitySmallForest
import ForestUnimodality.EdgeCounting
import ForestUnimodality.EdgeLowerBound
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Exact arbitrary-activity statistics for the small tree branch types.
The two rooted three-vertex types are distinguished by the independent-pair
count after deleting the root, not by a sampled or labeled catalogue. -/
namespace ForestUnimodality.ActivityPointDensitySmall

open Finset
variable {V : Type*} [DecidableEq V]

theorem statistics_card_one (G : SimpleGraph V) (S : Finset V)
    (hS : S.card = 1) (z : ℝ) :
    partitionFunction G S z = 1 + z ∧ hardCoreMomentNumerator G S 1 z = z := by
  have hZ := hardCoreMomentNumerator_eq_cardinality_sum G S 0 z
  have hM := hardCoreMomentNumerator_eq_cardinality_sum G S 1 z
  rw [hardCoreMomentNumerator_zero] at hZ
  norm_num [hS, sum_range_succ] at hZ hM
  exact ⟨hZ, hM⟩

theorem statistics_card_two (G : SimpleGraph V) (S : Finset V)
    (hS : S.card = 2) (z : ℝ) :
    partitionFunction G S z = 1 + 2 * z + countIndependent G S 2 * z ^ 2 ∧
    hardCoreMomentNumerator G S 1 z = 2 * z + 2 * countIndependent G S 2 * z ^ 2 := by
  have hZ := hardCoreMomentNumerator_eq_cardinality_sum G S 0 z
  have hM := hardCoreMomentNumerator_eq_cardinality_sum G S 1 z
  rw [hardCoreMomentNumerator_zero] at hZ
  norm_num [hS, sum_range_succ] at hZ hM
  constructor <;> nlinarith

theorem statistics_card_three (G : SimpleGraph V) (S : Finset V)
    (hS : S.card = 3) (z : ℝ) :
    partitionFunction G S z =
      1 + 3 * z + countIndependent G S 2 * z ^ 2 + countIndependent G S 3 * z ^ 3 ∧
    hardCoreMomentNumerator G S 1 z =
      3 * z + 2 * countIndependent G S 2 * z ^ 2 + 3 * countIndependent G S 3 * z ^ 3 := by
  have hZ := hardCoreMomentNumerator_eq_cardinality_sum G S 0 z
  have hM := hardCoreMomentNumerator_eq_cardinality_sum G S 1 z
  rw [hardCoreMomentNumerator_zero] at hZ
  norm_num [hS, sum_range_succ] at hZ hM
  constructor <;> nlinarith

theorem count_pair_eq_one_of_tree_card_three (G : SimpleGraph V) (S : Finset V)
    (hG : G.IsAcyclic) (hS : S.card = 3)
    (hconn : (G.induce (S : Set V)).Connected) : countIndependent G S 2 = 1 := by
  classical
  have htree : (G.induce (S : Set V)).IsTree := ⟨hconn, hG.induce (S : Set V)⟩
  have he := htree.card_edgeFinset
  rw [← edgeCountOn_eq_card_edgeFinset_induce,
    Fintype.card_of_finset' S (fun _ => Iff.rfl), hS] at he
  have hp := countIndependent_add_card_badSubsetsOn G S 2
  change countIndependent G S 2 + edgeCountOn G S = Nat.choose S.card 2 at hp
  norm_num [hS] at hp
  omega

theorem count_triple_eq_zero_of_tree_card_three (G : SimpleGraph V) (S : Finset V)
    (hG : G.IsAcyclic) (hS : S.card = 3)
    (hconn : (G.induce (S : Set V)).Connected) : countIndependent G S 3 = 0 := by
  classical
  have hpair := count_pair_eq_one_of_tree_card_three G S hG hS hconn
  have hnot : ¬G.IsIndepSet (S : Set V) := by
    intro hi
    have h := countIndependent_eq_choose_of_indep G S hi 2
    norm_num [hS, hpair] at h
  rw [countIndependent_eq_card_filter_powersetCard, ← hS]
  simp [hnot]

theorem tree_card_three_statistics (G : SimpleGraph V) (S : Finset V)
    (hG : G.IsAcyclic) (hS : S.card = 3)
    (hconn : (G.induce (S : Set V)).Connected) (z : ℝ) :
    partitionFunction G S z = 1 + 3 * z + z ^ 2 ∧
    hardCoreMomentNumerator G S 1 z = 3 * z + 2 * z ^ 2 := by
  obtain ⟨hZ, hM⟩ := statistics_card_three G S hS z
  have h2 := count_pair_eq_one_of_tree_card_three G S hG hS hconn
  have h3 := count_triple_eq_zero_of_tree_card_three G S hG hS hconn
  simpa only [h2, h3, Nat.cast_one, Nat.cast_zero, mul_one, one_mul, mul_zero, zero_mul,
    add_zero] using And.intro hZ hM

theorem tree_card_three_mean (G : SimpleGraph V) (S : Finset V)
    (hG : G.IsAcyclic) (hS : S.card = 3)
    (hconn : (G.induce (S : Set V)).Connected) (z : ℝ) :
    hardCoreMean G S z = (3 * z + 2 * z ^ 2) / (1 + 3 * z + z ^ 2) := by
  obtain ⟨hZ, hM⟩ := tree_card_three_statistics G S hG hS hconn z
  rw [hardCoreMean, hZ, hM]

theorem deleted_pair_cases (G : SimpleGraph V) (S : Finset V)
    (hS : S.card = 3) {u : V} (hu : u ∈ S) :
    countIndependent G (S.erase u) 2 = 0 ∨ countIndependent G (S.erase u) 2 = 1 := by
  have he : (S.erase u).card = 2 := by simpa [hS] using card_erase_of_mem hu
  have h := countIndependent_le_choose G (S.erase u) 2
  norm_num [he] at h
  omega

theorem deleted_endpoint_statistics (G : SimpleGraph V) (S : Finset V)
    (hG : G.IsAcyclic) (hS : S.card = 3)
    (hconn : (G.induce (S : Set V)).Connected) {u : V} (hu : u ∈ S)
    (ht : countIndependent G (S.erase u) 2 = 0) (z : ℝ) :
    hardCoreMean G (S.erase u) z = 2 * z / (1 + 2 * z) ∧
    partitionFunction G (S.erase u) z / partitionFunction G S z =
      (1 + 2 * z) / (1 + 3 * z + z ^ 2) := by
  have he : (S.erase u).card = 2 := by simpa [hS] using card_erase_of_mem hu
  obtain ⟨hZe, hMe⟩ := statistics_card_two G (S.erase u) he z
  obtain ⟨hZ, _⟩ := tree_card_three_statistics G S hG hS hconn z
  simp only [ht, Nat.cast_zero, mul_zero, zero_mul, add_zero] at hZe hMe
  exact ⟨by rw [hardCoreMean, hZe, hMe], by rw [hZe, hZ]⟩

theorem deleted_center_statistics (G : SimpleGraph V) (S : Finset V)
    (hG : G.IsAcyclic) (hS : S.card = 3)
    (hconn : (G.induce (S : Set V)).Connected) {u : V} (hu : u ∈ S)
    (ht : countIndependent G (S.erase u) 2 = 1) {z : ℝ} (hz : 0 ≤ z) :
    hardCoreMean G (S.erase u) z = 2 * z / (1 + z) ∧
    partitionFunction G (S.erase u) z / partitionFunction G S z =
      (1 + z) ^ 2 / (1 + 3 * z + z ^ 2) := by
  have he : (S.erase u).card = 2 := by simpa [hS] using card_erase_of_mem hu
  obtain ⟨hZe, hMe⟩ := statistics_card_two G (S.erase u) he z
  obtain ⟨hZ, _⟩ := tree_card_three_statistics G S hG hS hconn z
  simp only [ht, Nat.cast_one, mul_one, one_mul] at hZe hMe
  have hZe' : partitionFunction G (S.erase u) z = (1 + z) ^ 2 := by rw [hZe]; ring
  refine ⟨?_, by rw [hZe', hZ]⟩
  rw [hardCoreMean, hZe', hMe]
  have hz1 : 1 + z ≠ 0 := by positivity
  field_simp

#print axioms tree_card_three_statistics
#print axioms tree_card_three_mean
#print axioms deleted_pair_cases
#print axioms deleted_endpoint_statistics
#print axioms deleted_center_statistics

end ForestUnimodality.ActivityPointDensitySmall
