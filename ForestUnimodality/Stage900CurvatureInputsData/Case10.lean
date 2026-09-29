import ForestUnimodality.Stage900CurvatureInputs
import ForestUnimodality.Stage900CurvatureData.Case10

namespace ForestUnimodality.Stage900CurvatureInputsData.Case10
open Stage900CurvatureInputs Stage900CurvatureData.Case10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem scalar_valid : ScalarValid ⟨9,by decide⟩ parameters tilts := by
  constructor
  all_goals try norm_num [parameters, rates, tilts, Stage900SourceTable.base, Stage900SourceTable.row, SelectionSourceTable.row, qLower, qUpper, pathLower, pathVariance, CurvatureBudget.cut]
  all_goals intro j; fin_cases j <;> norm_num [parameters, rates, tilts, Stage900SourceTable.base, Stage900SourceTable.row, SelectionSourceTable.row, qLower, qUpper, pathLower, pathVariance, CurvatureBudget.cut]

variable {V : Type*} [DecidableEq V]

theorem actual_inputs {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 900≤S.card) (hz : z∈Set.Icc parameters.a parameters.b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    CurvatureBudgetGraph.Inputs parameters G S B z (hardCoreAvailableMean G S B z) k :=
  Stage900CurvatureInputs.actual_inputs ⟨9,by decide⟩ parameters tilts scalar_valid
    k hB hG hn hz hrank hmean

#print axioms scalar_valid
#print axioms actual_inputs
end ForestUnimodality.Stage900CurvatureInputsData.Case10
