import ForestUnimodality.SelectionSourceData.Case17.Batch00
import ForestUnimodality.SelectionSourceData.Case17.Batch01
import ForestUnimodality.SelectionSourceData.Case17.Batch02
import ForestUnimodality.SelectionSourceData.Case17.Batch03
import ForestUnimodality.SelectionSourceData.Case17.Batch04
import ForestUnimodality.SelectionSourceData.Case17.Batch05
import ForestUnimodality.SelectionSourceData.Case17.Batch06
import ForestUnimodality.SelectionSourceData.Case17.Batch07
import ForestUnimodality.SelectionSourceData.Case17.Batch08
import ForestUnimodality.SelectionSourceData.Case17.Batch09
import ForestUnimodality.SelectionSourceData.Case17.Batch10
import ForestUnimodality.SelectionSourceData.Case17.Batch11
import ForestUnimodality.SelectionSourceData.Case17.Batch12
import ForestUnimodality.SelectionSourceData.Case17.Batch13
import ForestUnimodality.SelectionSourceData.Case17.Batch14
import ForestUnimodality.SelectionSourceData.Case17.Batch15
import ForestUnimodality.SelectionSourceData.Case17.Batch16
import ForestUnimodality.SelectionSourceData.Case17.Batch17
import ForestUnimodality.SelectionSourceData.Case17.Batch18
import ForestUnimodality.SelectionSourceData.Case17.Batch19
import ForestUnimodality.SelectionSourceData.Case17.Batch20
import ForestUnimodality.SelectionSourceData.Case17.Batch21
import ForestUnimodality.SelectionSourceData.Case17.Batch22
import ForestUnimodality.SelectionSourceData.Case17.Batch23
import ForestUnimodality.SelectionSourceData.Case17.Batch24
import ForestUnimodality.SelectionSourceData.Case17.Batch25
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.SelectionSourceData.Case17
open SelectionSource
def cells : List Cell := Batch00.cells ++ Batch01.cells ++ Batch02.cells ++ Batch03.cells ++ Batch04.cells ++ Batch05.cells ++ Batch06.cells ++ Batch07.cells ++ Batch08.cells ++ Batch09.cells ++ Batch10.cells ++ Batch11.cells ++ Batch12.cells ++ Batch13.cells ++ Batch14.cells ++ Batch15.cells ++ Batch16.cells ++ Batch17.cells ++ Batch18.cells ++ Batch19.cells ++ Batch20.cells ++ Batch21.cells ++ Batch22.cells ++ Batch23.cells ++ Batch24.cells ++ Batch25.cells
theorem cells_checked : cells.all (fun c=>c.check parameters domain)=true := by
  simp only [cells,List.all_append,Batch00.cells_checked, Batch01.cells_checked, Batch02.cells_checked, Batch03.cells_checked, Batch04.cells_checked, Batch05.cells_checked, Batch06.cells_checked, Batch07.cells_checked, Batch08.cells_checked, Batch09.cells_checked, Batch10.cells_checked, Batch11.cells_checked, Batch12.cells_checked, Batch13.cells_checked, Batch14.cells_checked, Batch15.cells_checked, Batch16.cells_checked, Batch17.cells_checked, Batch18.cells_checked, Batch19.cells_checked, Batch20.cells_checked, Batch21.cells_checked, Batch22.cells_checked, Batch23.cells_checked, Batch24.cells_checked, Batch25.cells_checked,Bool.and_self]
theorem coverage_checked : SourceIntervalCoverage.check Cell.left Cell.right 0 (probabilityCap domain) cells=true := by decide +kernel

theorem source_valid : SelectionSourceRowValid parameters.toReal domain.lower domain.b :=
  sourceRowValid_of_checked parameters domain leaf cells parameters_checked domain_checked leaf_checked cells_checked coverage_checked

variable {V : Type*} [DecidableEq V]

/-- The actual common-activity total-occupancy variance and marginal score. -/
theorem forest_variance (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) {z : ℝ}
    (hzlo : ((27/25):ℝ)≤z) (hzhi : z≤((109/100):ℝ)) :
    hardCoreVariance G S z≤(987739/2000000)*hardCoreMarginalSelectionScore G S z (109/100)+(473691/2500000)*hardCoreMean G S z := by
  have hlo : (domain.lower:ℝ)≤z := by norm_num [domain]; exact hzlo
  have hhi : z≤(domain.b:ℝ) := by norm_num [domain]; exact hzhi
  have h := forest_selection_variance_of_scalar_certificate G hG S
    (ParametricSource.Domain.check_sound domain_checked).lower_pos hlo hhi parameters.toReal
    (Parameters.check_sound parameters_checked).1 source_valid
  norm_num [parameters,Parameters.toReal,domain] at h ⊢
  exact h

/-- The same actual maximizing marginal independent set used in the score bound. -/
theorem variance_le_mass {G : SimpleGraph V} {S I : Finset V} {z : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hzlo : ((27/25):ℝ)≤z) (hzhi : z≤((109/100):ℝ)) :
    hardCoreVariance G S z≤(8728223/10000000)*hardCoreOccupiedMass G S I z := by
  have hlo : (domain.lower:ℝ)≤z := by norm_num [domain]; exact hzlo
  have hhi : z≤(domain.b:ℝ) := by norm_num [domain]; exact hzhi
  have hP := Parameters.check_sound parameters_checked
  have h := hI.variance_le_mass_of_selection_certificate hG
    (ParametricSource.Domain.check_sound domain_checked).lower_pos hlo hhi parameters.toReal
    hP.1 hP.2.1 hP.2.2 source_valid
  norm_num [parameters,Parameters.toReal] at h ⊢
  exact h

#print axioms source_valid
#print axioms forest_variance
#print axioms variance_le_mass
end ForestUnimodality.SelectionSourceData.Case17
