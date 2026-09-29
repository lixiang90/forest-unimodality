import ForestUnimodality.Stage900CurvatureInputsData.Case06
import ForestUnimodality.Stage900CurvatureInputsData.Case07
import ForestUnimodality.Stage900CurvatureInputsData.Case08
import ForestUnimodality.Stage900CurvatureInputsData.Case09
import ForestUnimodality.Stage900CurvatureInputsData.Case10
import ForestUnimodality.Stage900CurvatureInputsData.Case11
import ForestUnimodality.Stage900CurvatureInputsData.Case12
import ForestUnimodality.Stage900CurvatureInputsData.Case13
import ForestUnimodality.Stage900CurvatureInputsData.Case14
import ForestUnimodality.Stage900CurvatureInputsData.Case15
import ForestUnimodality.Stage900CurvatureInputsData.Case16
import ForestUnimodality.Stage900CurvatureInputsData.Case17
import ForestUnimodality.Stage900CurvatureInputsData.Case18
import ForestUnimodality.Stage900CurvatureInputsData.Case19
import ForestUnimodality.Stage900CurvatureInputsData.Case20
import ForestUnimodality.Stage900CurvatureInputsData.Case21
import ForestUnimodality.Stage900CurvatureInputsData.Case22
import ForestUnimodality.Stage900CurvatureTable
import ForestUnimodality.CurvatureCoefficient

/-! Actual central curvature on the complete continuous stage-900 window.
Every variance, source, tail, numeric and half-line condition is discharged. -/
namespace ForestUnimodality.Stage900ActualCurvature
open Set Stage900CurvatureTable
variable {V : Type*} [DecidableEq V]

theorem actual_inputs (i : Fin 17) {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 900≤S.card) (hz : z∈Icc (row i).a (row i).b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    CurvatureBudgetGraph.Inputs (row i) G S B z (hardCoreAvailableMean G S B z) k := by
  fin_cases i
  · exact Stage900CurvatureInputsData.Case06.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case07.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case08.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case09.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case10.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case11.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case12.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case13.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case14.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case15.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case16.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case17.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case18.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case19.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case20.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case21.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage900CurvatureInputsData.Case22.actual_inputs k hB hG hn hz hrank hmean

theorem actual_positive (i : Fin 17) {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 900≤S.card) (hk : 1≤k) (hz : z∈Icc (row i).a (row i).b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    0<tiltedCenter (countIndependent G S) z (partitionFunction G S z) k :=
  CurvatureBudgetGraph.actual_positive (row_valid i) (margin_positive i)
    (actual_inputs i k hB hG hn hz hrank hmean) hk

theorem central_window_positive {G : SimpleGraph V} {S : Finset V} {z : ℝ} (k : ℕ)
    (hG : G.IsAcyclic) (hn : 900≤S.card) (hlo : (22/25:ℝ)≤z) (hhi : z≤(57/50:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    0<tiltedCenter (countIndependent G S) z (partitionFunction G S z) k := by
  obtain ⟨i,hzi⟩:=covers hlo hhi
  obtain ⟨B,hB⟩:=exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  have hnR : (900:ℝ)≤S.card := by exact_mod_cast hn
  have hkR : (1:ℝ)≤(k:ℝ) := by linarith
  have hk : 1≤k := by exact_mod_cast hkR
  exact actual_positive i k hB hG hn hk hzi hrank hmean

theorem central_window_strict_logConcavity {G : SimpleGraph V} {S : Finset V} {z : ℝ} (k : ℕ)
    (hG : G.IsAcyclic) (hn : 900≤S.card) (hlo : (22/25:ℝ)≤z) (hhi : z≤(57/50:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    countIndependent G S (k-1)*countIndependent G S (k+1)<countIndependent G S k^2 := by
  have hz : 0<z := by linarith
  have hnR : (900:ℝ)≤S.card := by exact_mod_cast hn
  have hkR : (1:ℝ)≤(k:ℝ) := by linarith
  have hk : 1≤k := by exact_mod_cast hkR
  exact coefficient_strict_logConcavity_of_tiltedCenter (countIndependent G S) hz
    (partitionFunction_pos G S hz.le) hk (central_window_positive k hG hn hlo hhi hrank hmean)

#print axioms actual_inputs
#print axioms actual_positive
#print axioms central_window_positive
#print axioms central_window_strict_logConcavity
end ForestUnimodality.Stage900ActualCurvature
