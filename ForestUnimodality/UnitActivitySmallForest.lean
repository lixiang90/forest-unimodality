import ForestUnimodality.HardCoreMixtureMoments
import ForestUnimodality.HardCoreActivityWindow
import ForestUnimodality.PathLowerBound

/-! Actual uniform independent-set means for the small branch types. The
three-vertex forest bound follows from its genuine independent-pair count;
no catalogue of labeled graphs or statistical premise is used. -/
namespace ForestUnimodality.UnitActivitySmallForest

open Finset
variable {V : Type*} [DecidableEq V]

theorem statistics_card_zero (G : SimpleGraph V) (S : Finset V) (hS : S.card = 0) :
    partitionFunction G S (1 : ℝ) = 1 ∧ hardCoreMomentNumerator G S 1 1 = 0 := by
  have hZ := hardCoreMomentNumerator_eq_cardinality_sum G S 0 1
  have hM := hardCoreMomentNumerator_eq_cardinality_sum G S 1 1
  rw [hardCoreMomentNumerator_zero] at hZ
  norm_num [hS, sum_range_succ] at hZ hM
  exact ⟨hZ, hM⟩

theorem statistics_card_one (G : SimpleGraph V) (S : Finset V) (hS : S.card = 1) :
    partitionFunction G S (1 : ℝ) = 2 ∧ hardCoreMomentNumerator G S 1 1 = 1 := by
  have hZ := hardCoreMomentNumerator_eq_cardinality_sum G S 0 1
  have hM := hardCoreMomentNumerator_eq_cardinality_sum G S 1 1
  rw [hardCoreMomentNumerator_zero] at hZ
  norm_num [hS, sum_range_succ] at hZ hM
  exact ⟨hZ, hM⟩

theorem statistics_card_two (G : SimpleGraph V) (S : Finset V) (hS : S.card = 2) :
    partitionFunction G S (1 : ℝ) = 3 + countIndependent G S 2 ∧
      hardCoreMomentNumerator G S 1 1 = 2 + 2 * countIndependent G S 2 := by
  have hZ := hardCoreMomentNumerator_eq_cardinality_sum G S 0 1
  have hM := hardCoreMomentNumerator_eq_cardinality_sum G S 1 1
  rw [hardCoreMomentNumerator_zero] at hZ
  norm_num [hS, sum_range_succ] at hZ hM
  constructor <;> linarith

theorem statistics_card_three (G : SimpleGraph V) (S : Finset V) (hS : S.card = 3) :
    partitionFunction G S (1 : ℝ) = 4 + countIndependent G S 2 + countIndependent G S 3 ∧
      hardCoreMomentNumerator G S 1 1 =
        3 + 2 * countIndependent G S 2 + 3 * countIndependent G S 3 := by
  have hZ := hardCoreMomentNumerator_eq_cardinality_sum G S 0 1
  have hM := hardCoreMomentNumerator_eq_cardinality_sum G S 1 1
  rw [hardCoreMomentNumerator_zero] at hZ
  norm_num [hS, sum_range_succ] at hZ hM
  constructor <;> linarith

theorem mean_eq_zero_of_card_zero (G : SimpleGraph V) (S : Finset V) (hS : S.card = 0) :
    hardCoreMean G S 1 = 0 := by
  obtain ⟨hZ, hM⟩ := statistics_card_zero G S hS
  simp [hardCoreMean, hZ, hM]

theorem mean_eq_half_of_card_one (G : SimpleGraph V) (S : Finset V) (hS : S.card = 1) :
    hardCoreMean G S 1 = 1 / 2 := by
  obtain ⟨hZ, hM⟩ := statistics_card_one G S hS
  simp [hardCoreMean, hZ, hM]

theorem mean_ge_two_thirds_of_card_two (G : SimpleGraph V) (S : Finset V) (hS : S.card = 2) :
    2 / 3 ≤ hardCoreMean G S 1 := by
  obtain ⟨hZ, hM⟩ := statistics_card_two G S hS
  have hpos := partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 1)
  unfold hardCoreMean
  apply (le_div_iff₀ hpos).mpr
  rw [hZ, hM]
  have hnonneg : (0 : ℝ) ≤ countIndependent G S 2 := Nat.cast_nonneg _
  linarith

theorem mean_ge_one_of_forest_card_three (G : SimpleGraph V) (S : Finset V)
    (hG : G.IsAcyclic) (hS : S.card = 3) : 1 ≤ hardCoreMean G S 1 := by
  have hp := choose_path_le_countIndependent G hG S 2
  norm_num [hS] at hp
  have hp' : (1 : ℝ) ≤ countIndependent G S 2 := by exact_mod_cast hp
  have h3 : (0 : ℝ) ≤ countIndependent G S 3 := Nat.cast_nonneg _
  obtain ⟨hZ, hM⟩ := statistics_card_three G S hS
  unfold hardCoreMean
  apply (le_div_iff₀ (partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 1))).mpr
  rw [hZ, hM]
  linarith

theorem deleted_ratio_bounds (G : SimpleGraph V) (S : Finset V) {u : V} (hu : u ∈ S) :
    1 / 2 ≤ partitionFunction G (S.erase u) (1 : ℝ) / partitionFunction G S 1 ∧
      partitionFunction G (S.erase u) (1 : ℝ) / partitionFunction G S 1 ≤ 1 := by
  have hZ := partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 1)
  have hA := partitionFunction_pos G (S.erase u) (by norm_num : (0 : ℝ) ≤ 1)
  have h := partitionFunction_delete_ratio_bounds G S hu (by norm_num : (0 : ℝ) ≤ 1)
  have hlo := (le_div_iff₀ hA).mp h.1
  have hhi := (div_le_iff₀ hA).mp h.2
  constructor
  · apply (le_div_iff₀ hZ).mpr
    linarith
  · apply (div_le_iff₀ hZ).mpr
    linarith

theorem singleton_statistics (G : SimpleGraph V) (S : Finset V) (hS : S.card = 1)
    {u : V} (hu : u ∈ S) :
    hardCoreMean G S 1 = 1 / 2 ∧ hardCoreMean G (S.erase u) 1 = 0 ∧
      partitionFunction G (S.erase u) (1 : ℝ) / partitionFunction G S 1 = 1 / 2 := by
  have he : (S.erase u).card = 0 := by simpa [hS] using card_erase_of_mem hu
  refine ⟨mean_eq_half_of_card_one G S hS, mean_eq_zero_of_card_zero G _ he, ?_⟩
  rw [(statistics_card_zero G _ he).1, (statistics_card_one G S hS).1]

theorem count_pair_eq_zero_of_connected_card_two (G : SimpleGraph V) (S : Finset V)
    (hS : S.card = 2) (hconn : (G.induce (S : Set V)).Connected) :
    countIndependent G S 2 = 0 := by
  classical
  have hnot : ¬G.IsIndepSet (S : Set V) := by
    intro hi
    obtain ⟨u, v, huv, heq⟩ := card_eq_two.mp hS
    have hu : u ∈ S := by simp [heq]
    have hv : v ∈ S := by simp [heq]
    have hne : (⟨u, hu⟩ : (S : Set V)) ≠ ⟨v, hv⟩ := fun he => huv (congrArg Subtype.val he)
    obtain ⟨w, hw⟩ := (hconn.preconnected ⟨u, hu⟩ ⟨v, hv⟩).nonempty_neighborSet_left hne
    have hadj : G.Adj u w.1 := hw
    exact hi hu w.2 hadj.ne hadj
  rw [countIndependent_eq_card_filter_powersetCard, ← hS]
  simp [hnot]

theorem edge_statistics (G : SimpleGraph V) (S : Finset V) (hS : S.card = 2)
    (hconn : (G.induce (S : Set V)).Connected) {u : V} (hu : u ∈ S) :
    hardCoreMean G S 1 = 2 / 3 ∧ hardCoreMean G (S.erase u) 1 = 1 / 2 ∧
      partitionFunction G (S.erase u) (1 : ℝ) / partitionFunction G S 1 = 2 / 3 := by
  have he : (S.erase u).card = 1 := by simpa [hS] using card_erase_of_mem hu
  have hc := count_pair_eq_zero_of_connected_card_two G S hS hconn
  obtain ⟨hZ, hM⟩ := statistics_card_two G S hS
  norm_num [hc] at hZ hM
  refine ⟨?_, mean_eq_half_of_card_one G _ he, ?_⟩
  · simp [hardCoreMean, hZ, hM]
  · rw [(statistics_card_one G _ he).1, hZ]

theorem three_statistics (G : SimpleGraph V) (S : Finset V) (hG : G.IsAcyclic)
    (hS : S.card = 3) {u : V} (hu : u ∈ S) :
    1 ≤ hardCoreMean G S 1 ∧ 2 / 3 ≤ hardCoreMean G (S.erase u) 1 ∧
      1 / 2 ≤ partitionFunction G (S.erase u) (1 : ℝ) / partitionFunction G S 1 ∧
      partitionFunction G (S.erase u) (1 : ℝ) / partitionFunction G S 1 ≤ 1 := by
  have he : (S.erase u).card = 2 := by simpa [hS] using card_erase_of_mem hu
  exact ⟨mean_ge_one_of_forest_card_three G S hG hS,
    mean_ge_two_thirds_of_card_two G _ he, deleted_ratio_bounds G S hu⟩

#print axioms mean_ge_two_thirds_of_card_two
#print axioms mean_ge_one_of_forest_card_three
#print axioms deleted_ratio_bounds
#print axioms singleton_statistics
#print axioms edge_statistics
#print axioms three_statistics
end ForestUnimodality.UnitActivitySmallForest
