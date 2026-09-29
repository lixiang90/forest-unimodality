import ForestUnimodality.Stage350PlainActualDirection
import ForestUnimodality.Stage350PlainDirectionAllOrders

/-! The old analytic rows apply whenever the actual available mean
exceeds their start, including forests with fewer than 350 vertices. -/
namespace ForestUnimodality.Stage350PlainAllOrders
open Set Stage350PlainDirectionTable Stage350PlainActualDirection
variable {V : Type*} [DecidableEq V]

theorem actual_inputs (i : Fin 11) {G : SimpleGraph V} {S B : Finset V}
    {z : ℝ} (k : ℕ) (hB : IsMaximumMarginalIndependentOn G S B z)
    (hG : G.IsAcyclic) (hn : 0 < S.card)
    (hs : (row i).start ≤ hardCoreAvailableMean G S B z)
    (hz : z ∈ Icc (row i).a (row i).b)
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k) :
    DirectionBudgetGraph.Inputs (row i) G S B z (hardCoreAvailableMean G S B z)
      k (profile0 i) (profile1 i) := by
  fin_cases i
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 0
      Stage350PlainDirectionData.Case01.parameters Stage350PlainDirectionData.Case01.parameters_valid
      Stage350PlainInputsData.Case01.profile0 Stage350PlainInputsData.Case01.profile1 Stage350PlainInputsData.Case01.source0 Stage350PlainInputsData.Case01.source1
      Stage350PlainInputsData.Case01.tilt0 Stage350PlainInputsData.Case01.tilt1 Stage350PlainInputsData.Case01.scalar_valid
      k hB hG hn hs hz hrank hmean
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 1
      Stage350PlainDirectionData.Case02.parameters Stage350PlainDirectionData.Case02.parameters_valid
      Stage350PlainInputsData.Case02.profile0 Stage350PlainInputsData.Case02.profile1 Stage350PlainInputsData.Case02.source0 Stage350PlainInputsData.Case02.source1
      Stage350PlainInputsData.Case02.tilt0 Stage350PlainInputsData.Case02.tilt1 Stage350PlainInputsData.Case02.scalar_valid
      k hB hG hn hs hz hrank hmean
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 2
      Stage350PlainDirectionData.Case03.parameters Stage350PlainDirectionData.Case03.parameters_valid
      Stage350PlainInputsData.Case03.profile0 Stage350PlainInputsData.Case03.profile1 Stage350PlainInputsData.Case03.source0 Stage350PlainInputsData.Case03.source1
      Stage350PlainInputsData.Case03.tilt0 Stage350PlainInputsData.Case03.tilt1 Stage350PlainInputsData.Case03.scalar_valid
      k hB hG hn hs hz hrank hmean
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 35
      Stage350PlainDirectionData.Case36.parameters Stage350PlainDirectionData.Case36.parameters_valid
      Stage350PlainInputsData.Case36.profile0 Stage350PlainInputsData.Case36.profile1 Stage350PlainInputsData.Case36.source0 Stage350PlainInputsData.Case36.source1
      Stage350PlainInputsData.Case36.tilt0 Stage350PlainInputsData.Case36.tilt1 Stage350PlainInputsData.Case36.scalar_valid
      k hB hG hn hs hz hrank hmean
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 36
      Stage350PlainDirectionData.Case37.parameters Stage350PlainDirectionData.Case37.parameters_valid
      Stage350PlainInputsData.Case37.profile0 Stage350PlainInputsData.Case37.profile1 Stage350PlainInputsData.Case37.source0 Stage350PlainInputsData.Case37.source1
      Stage350PlainInputsData.Case37.tilt0 Stage350PlainInputsData.Case37.tilt1 Stage350PlainInputsData.Case37.scalar_valid
      k hB hG hn hs hz hrank hmean
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 37
      Stage350PlainDirectionData.Case38.parameters Stage350PlainDirectionData.Case38.parameters_valid
      Stage350PlainInputsData.Case38.profile0 Stage350PlainInputsData.Case38.profile1 Stage350PlainInputsData.Case38.source0 Stage350PlainInputsData.Case38.source1
      Stage350PlainInputsData.Case38.tilt0 Stage350PlainInputsData.Case38.tilt1 Stage350PlainInputsData.Case38.scalar_valid
      k hB hG hn hs hz hrank hmean
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 38
      Stage350PlainDirectionData.Case39.parameters Stage350PlainDirectionData.Case39.parameters_valid
      Stage350PlainInputsData.Case39.profile0 Stage350PlainInputsData.Case39.profile1 Stage350PlainInputsData.Case39.source0 Stage350PlainInputsData.Case39.source1
      Stage350PlainInputsData.Case39.tilt0 Stage350PlainInputsData.Case39.tilt1 Stage350PlainInputsData.Case39.scalar_valid
      k hB hG hn hs hz hrank hmean
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 39
      Stage350PlainDirectionData.Case40.parameters Stage350PlainDirectionData.Case40.parameters_valid
      Stage350PlainInputsData.Case40.profile0 Stage350PlainInputsData.Case40.profile1 Stage350PlainInputsData.Case40.source0 Stage350PlainInputsData.Case40.source1
      Stage350PlainInputsData.Case40.tilt0 Stage350PlainInputsData.Case40.tilt1 Stage350PlainInputsData.Case40.scalar_valid
      k hB hG hn hs hz hrank hmean
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 40
      Stage350PlainDirectionData.Case41.parameters Stage350PlainDirectionData.Case41.parameters_valid
      Stage350PlainInputsData.Case41.profile0 Stage350PlainInputsData.Case41.profile1 Stage350PlainInputsData.Case41.source0 Stage350PlainInputsData.Case41.source1
      Stage350PlainInputsData.Case41.tilt0 Stage350PlainInputsData.Case41.tilt1 Stage350PlainInputsData.Case41.scalar_valid
      k hB hG hn hs hz hrank hmean
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 41
      Stage350PlainDirectionData.Case42.parameters Stage350PlainDirectionData.Case42.parameters_valid
      Stage350PlainInputsData.Case42.profile0 Stage350PlainInputsData.Case42.profile1 Stage350PlainInputsData.Case42.source0 Stage350PlainInputsData.Case42.source1
      Stage350PlainInputsData.Case42.tilt0 Stage350PlainInputsData.Case42.tilt1 Stage350PlainInputsData.Case42.scalar_valid
      k hB hG hn hs hz hrank hmean
  · exact Stage350PlainDirectionAllOrders.actual_inputs_of_start 42
      Stage350PlainDirectionData.Case43.parameters Stage350PlainDirectionData.Case43.parameters_valid
      Stage350PlainInputsData.Case43.profile0 Stage350PlainInputsData.Case43.profile1 Stage350PlainInputsData.Case43.source0 Stage350PlainInputsData.Case43.source1
      Stage350PlainInputsData.Case43.tilt0 Stage350PlainInputsData.Case43.tilt1 Stage350PlainInputsData.Case43.scalar_valid
      k hB hG hn hs hz hrank hmean

theorem source_start_eq (i : Fin 11) :
    (row i).start = ((Stage350SourceTable.row (sourceIndex i)).start : ℝ) := by
  fin_cases i
  · exact Stage350PlainInputsData.Case01.scalar_valid.start_match
  · exact Stage350PlainInputsData.Case02.scalar_valid.start_match
  · exact Stage350PlainInputsData.Case03.scalar_valid.start_match
  · exact Stage350PlainInputsData.Case36.scalar_valid.start_match
  · exact Stage350PlainInputsData.Case37.scalar_valid.start_match
  · exact Stage350PlainInputsData.Case38.scalar_valid.start_match
  · exact Stage350PlainInputsData.Case39.scalar_valid.start_match
  · exact Stage350PlainInputsData.Case40.scalar_valid.start_match
  · exact Stage350PlainInputsData.Case41.scalar_valid.start_match
  · exact Stage350PlainInputsData.Case42.scalar_valid.start_match
  · exact Stage350PlainInputsData.Case43.scalar_valid.start_match

theorem actual_left_coefficient_lt (i : Fin 11) (hi : isLeft i = true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 0 < S.card) (hs : (row i).start ≤ hardCoreAvailableMean G S B z)
    (hz : z ∈ Icc (row i).a (row i).b)
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k) (hk : 1 ≤ k) :
    countIndependent G S (k - 1) < countIndependent G S k :=
  DirectionBudgetGraph.actual_left_coefficient_lt (row_valid i)
    (actual_inputs i k hB hG hn hs hz hrank hmean) hk (left_upper i hi)
    (bracket_positive i).le (mass_positive i).le
    (by simpa only [hi, ↓reduceIte] using margin_positive i)

theorem actual_right_coefficient_lt (i : Fin 11) (hi : isLeft i = false)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 0 < S.card) (hs : (row i).start ≤ hardCoreAvailableMean G S B z)
    (hz : z ∈ Icc (row i).a (row i).b)
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k) :
    countIndependent G S (k + 1) < countIndependent G S k :=
  DirectionBudgetGraph.actual_right_coefficient_lt (row_valid i)
    (actual_inputs i k hB hG hn hs hz hrank hmean) (right_lower i hi)
    (bracket_positive i).le (mass_positive i).le
    (by simpa only [hi, Bool.false_eq_true, ↓reduceIte] using margin_positive i)

theorem no_weak_valley_of_start (i : Fin 11)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 0 < S.card) (hs : (row i).start ≤ hardCoreAvailableMean G S B z)
    (hz : z ∈ Icc (row i).a (row i).b)
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = k) (hk : 1 ≤ k) :
    ¬ (countIndependent G S k ≤ countIndependent G S (k - 1) ∧
      countIndependent G S k ≤ countIndependent G S (k + 1)) := by
  intro hvalley
  cases hi : isLeft i with
  | true =>
      exact (not_lt_of_ge hvalley.1)
        (actual_left_coefficient_lt i hi k hB hG hn hs hz hrank hmean hk)
  | false =>
      exact (not_lt_of_ge hvalley.2)
        (actual_right_coefficient_lt i hi k hB hG hn hs hz hrank hmean)

#print axioms actual_inputs
#print axioms source_start_eq
#print axioms actual_left_coefficient_lt
#print axioms actual_right_coefficient_lt
#print axioms no_weak_valley_of_start
end ForestUnimodality.Stage350PlainAllOrders
