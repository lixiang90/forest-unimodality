import ForestUnimodality.Stage80ConstantData.Case26.Batch00
import ForestUnimodality.Stage80ConstantData.Case26.Batch01
import ForestUnimodality.Stage80ConstantData.Case26.Batch02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.Stage80ConstantData.Case26
def cells : List ExactSelectionSource.Cell := Batch00.cells ++ Batch01.cells ++ Batch02.cells
theorem cells_checked : cells.all (fun c=>c.check parameters domain)=true := by
  simp only [cells,List.all_append,Batch00.cells_checked, Batch01.cells_checked, Batch02.cells_checked,Bool.and_self]
theorem coverage_checked : SourceIntervalCoverage.check ExactSelectionSource.Cell.left ExactSelectionSource.Cell.right
    0 (SelectionSource.probabilityCap domain) cells=true := by decide +kernel

theorem source_valid : MessageSourceRowValid (ExactSelectionSource.toMessage parameters) domain.lower domain.b :=
  ExactSelectionSource.sourceRowValid_of_checked parameters domain leafH leafLog leaf cells
    parameters_checked domain_checked leaf_checked cells_checked coverage_checked

variable {V : Type*} [DecidableEq V]

/-- True common-activity forest variance with the exact capacity source. -/
theorem forest_variance (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) {z : ℝ}
    (hzlo : ((97/80):ℝ)≤z) (hzhi : z≤((49/40):ℝ)) :
    hardCoreVariance G S z≤(2458773/5000000)*hardCoreMarginalSelectionScore G S z (49/40)+(1868711/10000000)*hardCoreMean G S z := by
  have hlo : (domain.lower:ℝ)≤z := by norm_num [domain]; exact hzlo
  have hhi : z≤(domain.b:ℝ) := by norm_num [domain]; exact hzhi
  have h := ExactSelectionSource.forest_variance parameters parameters_checked G hG S
    (ParametricSource.Domain.check_sound domain_checked).lower_pos hlo hhi source_valid
  norm_num [parameters,domain] at h ⊢
  exact h

theorem variance_le_mass {G : SimpleGraph V} {S I : Finset V} {z : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hzlo : ((97/80):ℝ)≤z) (hzhi : z≤((49/40):ℝ)) :
    hardCoreVariance G S z≤(1081871/1250000)*hardCoreOccupiedMass G S I z := by
  have hlo : (domain.lower:ℝ)≤z := by norm_num [domain]; exact hzlo
  have hhi : z≤(domain.b:ℝ) := by norm_num [domain]; exact hzhi
  have h := ExactSelectionSource.variance_le_mass parameters parameters_checked hI hG
    (ParametricSource.Domain.check_sound domain_checked).lower_pos hlo hhi source_valid
  norm_num [parameters] at h ⊢
  exact h

#print axioms source_valid
#print axioms forest_variance
#print axioms variance_le_mass
end ForestUnimodality.Stage80ConstantData.Case26
