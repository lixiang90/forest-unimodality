import ForestUnimodality.Stage900DirectionInputs
import ForestUnimodality.Stage900DirectionData.Case28

namespace ForestUnimodality.Stage900DirectionInputsData.Case28
open Stage900DirectionInputs ReciprocalGradientBudget
open Stage900DirectionData.Case28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0 : GradientProfile := .general 0
def profile1 : GradientProfile := .general 0
def tilt0 : ℚ := 50700000000000000000000000000000/363201706916283653695411151212769
def tilt1 : ℚ := 57037500000000000000000000000000/365301706916283653695411151212769

theorem scalar_valid : ScalarValid ⟨27, by decide⟩ parameters
    profile0 profile1 tilt0 tilt1 := by
  constructor
  all_goals try norm_num [parameters, Stage900SourceTable.base,
    Stage900SourceTable.row, SelectionSourceTable.row, qLower, qUpper,
    pathLower, pathVariance, ProfileRange, profile0, profile1, tilt0, tilt1,
    GradientProfile.constant, BinomialGradientTable.scale,
    BinomialGradientTable.generalConstant, BinomialGradientTable.nearConstant]


variable {V : Type*} [DecidableEq V]

theorem actual_inputs {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 900 ≤ S.card) (hz : z ∈ Set.Icc parameters.a parameters.b)
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    DirectionBudgetGraph.Inputs parameters G S B z (hardCoreAvailableMean G S B z)
      k profile0 profile1 :=
  Stage900DirectionInputs.actual_inputs ⟨27, by decide⟩ parameters parameters_valid
    profile0 profile1 tilt0 tilt1 scalar_valid k hB hG hn hz hrank hmean

#print axioms scalar_valid
#print axioms actual_inputs
end ForestUnimodality.Stage900DirectionInputsData.Case28
