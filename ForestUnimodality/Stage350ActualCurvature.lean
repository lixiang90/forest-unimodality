import ForestUnimodality.Stage350CurvatureInputsData.Case07
import ForestUnimodality.Stage350CurvatureInputsData.Case08
import ForestUnimodality.Stage350CurvatureInputsData.Case09
import ForestUnimodality.Stage350CurvatureInputsData.Case10
import ForestUnimodality.Stage350CurvatureInputsData.Case11
import ForestUnimodality.Stage350CurvatureInputsData.Case12
import ForestUnimodality.Stage350CurvatureInputsData.Case13
import ForestUnimodality.Stage350CurvatureInputsData.Case14
import ForestUnimodality.Stage350CurvatureInputsData.Case15
import ForestUnimodality.Stage350CurvatureInputsData.Case16
import ForestUnimodality.Stage350CurvatureInputsData.Case17
import ForestUnimodality.Stage350CurvatureInputsData.Case18
import ForestUnimodality.Stage350CurvatureInputsData.Case19
import ForestUnimodality.Stage350CurvatureInputsData.Case20
import ForestUnimodality.Stage350CurvatureInputsData.Case21
import ForestUnimodality.Stage350CurvatureInputsData.Case22
import ForestUnimodality.Stage350CurvatureInputsData.Case23
import ForestUnimodality.Stage350CurvatureTable
import ForestUnimodality.CurvatureCoefficient

/-! Actual central curvature on the complete continuous stage-350 window.
Every variance, source, tail, numeric and half-line condition is discharged. -/
namespace ForestUnimodality.Stage350ActualCurvature
open Set Stage350CurvatureTable
variable {V : Type*} [DecidableEq V]

theorem actual_inputs (i : Fin 17) {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 350≤S.card) (hz : z∈Icc (row i).a (row i).b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    Stage350CurvatureGraph.Inputs (row i) G S B z (hardCoreAvailableMean G S B z) k := by
  fin_cases i
  · exact Stage350CurvatureInputsData.Case07.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case08.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case09.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case10.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case11.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case12.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case13.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case14.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case15.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case16.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case17.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case18.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case19.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case20.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case21.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case22.actual_inputs k hB hG hn hz hrank hmean
  · exact Stage350CurvatureInputsData.Case23.actual_inputs k hB hG hn hz hrank hmean

theorem actual_positive (i : Fin 17) {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 350≤S.card) (hk : 1≤k) (hz : z∈Icc (row i).a (row i).b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    0<tiltedCenter (countIndependent G S) z (partitionFunction G S z) k :=
  Stage350CurvatureGraph.actual_positive (row_valid i) (main_positive i).le (margin_positive i) (bad_polynomial_nonpos i)
    (actual_inputs i k hB hG hn hz hrank hmean) hk

theorem actual_inputs_any_size (i : Fin 17) {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 0<S.card) (hz : z∈Icc (row i).a (row i).b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ))
    (hstart : (row i).start≤hardCoreAvailableMean G S B z) :
    Stage350CurvatureGraph.Inputs (row i) G S B z (hardCoreAvailableMean G S B z) k := by
  fin_cases i
  · exact Stage350CurvatureInputsData.Case07.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case08.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case09.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case10.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case11.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case12.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case13.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case14.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case15.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case16.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case17.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case18.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case19.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case20.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case21.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case22.actual_inputs_any_size k hB hG hn hz hrank hmean hstart
  · exact Stage350CurvatureInputsData.Case23.actual_inputs_any_size k hB hG hn hz hrank hmean hstart

theorem actual_positive_any_size (i : Fin 17) {G : SimpleGraph V} {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 0<S.card) (hk : 1≤k) (hz : z∈Icc (row i).a (row i).b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ))
    (hstart : (row i).start≤hardCoreAvailableMean G S B z) :
    0<tiltedCenter (countIndependent G S) z (partitionFunction G S z) k :=
  Stage350CurvatureGraph.actual_positive (row_valid i) (main_positive i).le
    (margin_positive i) (bad_polynomial_nonpos i)
    (actual_inputs_any_size i k hB hG hn hz hrank hmean hstart) hk

theorem actual_strict_logConcavity_any_size (i : Fin 17) {G : SimpleGraph V}
    {S B : Finset V} {z : ℝ} (k : ℕ)
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 0<S.card) (hk : 1≤k) (hz : z∈Icc (row i).a (row i).b)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ))
    (hstart : (row i).start≤hardCoreAvailableMean G S B z) :
    countIndependent G S (k-1)*countIndependent G S (k+1)<countIndependent G S k^2 := by
  have hinputs:=actual_inputs_any_size i k hB hG hn hz hrank hmean hstart
  exact coefficient_strict_logConcavity_of_tiltedCenter (countIndependent G S)
    hinputs.activity_pos (partitionFunction_pos G S hinputs.activity_pos.le) hk
    (actual_positive_any_size i k hB hG hn hk hz hrank hmean hstart)

theorem central_window_positive {G : SimpleGraph V} {S : Finset V} {z : ℝ} (k : ℕ)
    (hG : G.IsAcyclic) (hn : 350≤S.card) (hlo : (22/25:ℝ)≤z) (hhi : z≤(57/50:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    0<tiltedCenter (countIndependent G S) z (partitionFunction G S z) k := by
  obtain ⟨i,hzi⟩:=covers hlo hhi
  obtain ⟨B,hB⟩:=exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  have hnR : (350:ℝ)≤S.card := by exact_mod_cast hn
  have hkR : (1:ℝ)≤(k:ℝ) := by linarith
  have hk : 1≤k := by exact_mod_cast hkR
  exact actual_positive i k hB hG hn hk hzi hrank hmean

theorem central_window_strict_logConcavity {G : SimpleGraph V} {S : Finset V} {z : ℝ} (k : ℕ)
    (hG : G.IsAcyclic) (hn : 350≤S.card) (hlo : (22/25:ℝ)≤z) (hhi : z≤(57/50:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z)
    (hmean : hardCoreMean G S z=(k:ℝ)) :
    countIndependent G S (k-1)*countIndependent G S (k+1)<countIndependent G S k^2 := by
  have hz : 0<z := by linarith
  have hnR : (350:ℝ)≤S.card := by exact_mod_cast hn
  have hkR : (1:ℝ)≤(k:ℝ) := by linarith
  have hk : 1≤k := by exact_mod_cast hkR
  exact coefficient_strict_logConcavity_of_tiltedCenter (countIndependent G S) hz
    (partitionFunction_pos G S hz.le) hk (central_window_positive k hG hn hlo hhi hrank hmean)

#print axioms actual_inputs
#print axioms actual_positive
#print axioms actual_inputs_any_size
#print axioms actual_positive_any_size
#print axioms actual_strict_logConcavity_any_size
#print axioms central_window_positive
#print axioms central_window_strict_logConcavity
end ForestUnimodality.Stage350ActualCurvature
