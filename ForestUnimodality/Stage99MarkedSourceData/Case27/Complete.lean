import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch00
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch01
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch02
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch03
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch04
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch05
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch06
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch07
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch08
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch09
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch10
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch11
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch12
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch13
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch14
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch15
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch16
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch17
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch18
import ForestUnimodality.Stage99MarkedSourceData.Case27.Batch19
import ForestUnimodality.SourceGeneralAssembly
import ForestUnimodality.SourceMixtureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.Stage99MarkedSourceData.Case27
open ParametricSource
def cells : List Cell := Batch00.cells ++ Batch01.cells ++ Batch02.cells ++ Batch03.cells ++ Batch04.cells ++ Batch05.cells ++ Batch06.cells ++ Batch07.cells ++ Batch08.cells ++ Batch09.cells ++ Batch10.cells ++ Batch11.cells ++ Batch12.cells ++ Batch13.cells ++ Batch14.cells ++ Batch15.cells ++ Batch16.cells ++ Batch17.cells ++ Batch18.cells ++ Batch19.cells
theorem cells_checked : cells.all (Cell.check parameters domain)=true := by
  simp only [cells,List.all_append,Batch00.cells_checked, Batch01.cells_checked, Batch02.cells_checked, Batch03.cells_checked, Batch04.cells_checked, Batch05.cells_checked, Batch06.cells_checked, Batch07.cells_checked, Batch08.cells_checked, Batch09.cells_checked, Batch10.cells_checked, Batch11.cells_checked, Batch12.cells_checked, Batch13.cells_checked, Batch14.cells_checked, Batch15.cells_checked, Batch16.cells_checked, Batch17.cells_checked, Batch18.cells_checked, Batch19.cells_checked,Bool.and_self]
theorem coverage_checked : SourceIntervalCoverage.check Cell.left Cell.right origin.delta
    (domain.b/(1+domain.b)) cells=true := by decide +kernel

theorem source_valid : SourceRowValid parameters.toReal domain.lower domain.b :=
  sourceRowValid_of_checked parameters domain origin leaf cells parameters_checked domain_checked
    origin_checked leaf_checked cells_checked coverage_checked

variable {V : Type*} [DecidableEq V]

/-- Actual heterogeneous forest occupation variance on [(9/10),(13/10)]. -/
theorem forest_marked_variance (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) (hB : G.IsIndepSet (B:Set V)) (activity : V→ℝ)
    (hactivity : ∀x∈S, ((9/10):ℝ)≤activity x ∧ activity x≤(13/10)) :
    heterogeneousVariance G S activity (fun J=>((J∩B).card:ℝ)) ≤
      (243069733/1000000000)*heterogeneousMean G S activity (fun J=>(J.card:ℝ))+
      (125664973/100000000)*heterogeneousMean G S activity (fun J=>((J∩B).card:ℝ)) := by
  have hact : ∀x∈S, (domain.lower:ℝ)≤activity x ∧ activity x≤(domain.b:ℝ) := by
    norm_num [domain]
    exact hactivity
  have h := forest_independent_count_variance_of_scalar_certificate G hG S B hB activity
    (Domain.check_sound domain_checked).lower_pos hact parameters.toReal
    (parameters.admissible_sound parameters_checked) source_valid
  norm_num [parameters,RationalSourceParameters.toReal] at h ⊢
  exact h

/-- Same fixed maximum marginal independent set and the actual availability law. -/
theorem available_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hzlo : ((9/10):ℝ)≤z) (hzhi : z≤(13/10)) :
    hardCoreAvailableVariance G S B z ≤
      (1+(185697299/250000000)/(z/(1+z)))*hardCoreAvailableMean G S B z := by
  have hlo : (domain.lower:ℝ)≤z := by norm_num [domain]; exact hzlo
  have hhi : z≤(domain.b:ℝ) := by norm_num [domain]; exact hzhi
  have h := hB.available_variance_le_of_source_certificate hG
    (Domain.check_sound domain_checked).lower_pos hlo hhi parameters.toReal
    (parameters.admissible_sound parameters_checked)
    (by norm_num [parameters,RationalSourceParameters.toReal]) source_valid
  norm_num [parameters,RationalSourceParameters.toReal] at h ⊢
  exact h

#print axioms source_valid
#print axioms forest_marked_variance
#print axioms available_variance
end ForestUnimodality.Stage99MarkedSourceData.Case27
