import ForestUnimodality.SelectionSourceData.Case25.Batch00
import ForestUnimodality.SelectionSourceData.Case25.Batch01
import ForestUnimodality.SelectionSourceData.Case25.Batch02
import ForestUnimodality.SelectionSourceData.Case25.Batch03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.SelectionSourceData.Case25
open SelectionSource
def cells : List Cell := Batch00.cells ++ Batch01.cells ++ Batch02.cells ++ Batch03.cells
theorem cells_checked : cells.all (fun c=>c.check parameters domain)=true := by
  simp only [cells,List.all_append,Batch00.cells_checked, Batch01.cells_checked, Batch02.cells_checked, Batch03.cells_checked,Bool.and_self]
theorem coverage_checked : SourceIntervalCoverage.check Cell.left Cell.right 0 (probabilityCap domain) cells=true := by decide +kernel

theorem source_valid : SelectionSourceRowValid parameters.toReal domain.lower domain.b :=
  sourceRowValid_of_checked parameters domain leaf cells parameters_checked domain_checked leaf_checked cells_checked coverage_checked

variable {V : Type*} [DecidableEq V]

/-- The actual common-activity total-occupancy variance and marginal score. -/
theorem forest_variance (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) {z : ℝ}
    (hzlo : ((6/5):ℝ)≤z) (hzhi : z≤((13/10):ℝ)) :
    hardCoreVariance G S z≤(2458773/5000000)*hardCoreMarginalSelectionScore G S z (13/10)+(2168711/10000000)*hardCoreMean G S z := by
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
    (hzlo : ((6/5):ℝ)≤z) (hzhi : z≤((13/10):ℝ)) :
    hardCoreVariance G S z≤(1156871/1250000)*hardCoreOccupiedMass G S I z := by
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
end ForestUnimodality.SelectionSourceData.Case25
