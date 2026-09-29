import ForestUnimodality.Stage900DirectionInputs
import ForestUnimodality.Stage900DirectionData.Case01

namespace ForestUnimodality.Stage900DirectionInputsData.Case01
open Stage900DirectionInputs ReciprocalGradientBudget
open Stage900DirectionData.Case01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0 : GradientProfile := .universal
def profile1 : GradientProfile := .universal
def tilt0 : ℚ := 973568750000000000000000000000000/2728924166666666666666666666671387
def tilt1 : ℚ := 1327593750000000000000000000000000/2926924166666666666666666666671387

theorem scalar_valid : ScalarValid ⟨0, by decide⟩ parameters
    profile0 profile1 tilt0 tilt1 := by
  constructor
  all_goals try norm_num [parameters, Stage900SourceTable.base,
    Stage900SourceTable.row, SelectionSourceTable.row, qLower, qUpper,
    pathLower, pathVariance, ProfileRange, profile0, profile1, tilt0, tilt1,
    GradientProfile.constant, BinomialGradientTable.scale,
    BinomialGradientTable.generalConstant, BinomialGradientTable.nearConstant]
  all_goals linarith [Real.pi_lt_d4]


variable {V : Type*} [DecidableEq V]

theorem actual_inputs {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 900 ≤ S.card) (hz : z ∈ Set.Icc parameters.a parameters.b)
    (hrank : (S.card : ℝ)/4 ≤ hardCoreMean G S z)
    (hmean : hardCoreMean G S z = (k : ℝ)) :
    DirectionBudgetGraph.Inputs parameters G S B z (hardCoreAvailableMean G S B z)
      k profile0 profile1 :=
  Stage900DirectionInputs.actual_inputs ⟨0, by decide⟩ parameters parameters_valid
    profile0 profile1 tilt0 tilt1 scalar_valid k hB hG hn hz hrank hmean

#print axioms scalar_valid
#print axioms actual_inputs
end ForestUnimodality.Stage900DirectionInputsData.Case01
