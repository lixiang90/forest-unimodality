import ForestUnimodality.SourceCaseOneData.Batch00
import ForestUnimodality.SourceCaseOneData.Batch01
import ForestUnimodality.SourceCaseOneData.Batch02
import ForestUnimodality.SourceCaseOneData.Batch03
import ForestUnimodality.SourceCaseOneData.Batch04
import ForestUnimodality.SourceCaseOneData.Batch05
import ForestUnimodality.SourceCaseOneData.Batch06
import ForestUnimodality.SourceCaseOneData.Batch07
import ForestUnimodality.SourceCaseOneData.Batch08
import ForestUnimodality.SourceCaseOneData.Batch09
import ForestUnimodality.SourceCaseOneData.Batch10
import ForestUnimodality.SourceCaseOneData.Batch11
import ForestUnimodality.SourceCaseOneData.Batch12
import ForestUnimodality.SourceCaseOneData.Batch13
import ForestUnimodality.SourceCaseOneData.Batch14
import ForestUnimodality.SourceCaseOneData.Batch15
import ForestUnimodality.SourceCaseOneData.Batch16
import ForestUnimodality.SourceCaseOneData.Batch17
import ForestUnimodality.SourceCaseOneData.Batch18
import ForestUnimodality.SourceCaseOneData.Batch19
import ForestUnimodality.SourceCaseOneData.Batch20
import ForestUnimodality.SourceCaseOneData.Batch21
import ForestUnimodality.SourceCaseOneData.Batch22
import ForestUnimodality.SourceScalarOrigin
import ForestUnimodality.SourceIntervalCoverage
import ForestUnimodality.SourceMixtureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality
namespace SourceCaseOneData
def cells : List SourceCellCertificate := Batch00.cells ++ Batch01.cells ++ Batch02.cells ++ Batch03.cells ++ Batch04.cells ++ Batch05.cells ++ Batch06.cells ++ Batch07.cells ++ Batch08.cells ++ Batch09.cells ++ Batch10.cells ++ Batch11.cells ++ Batch12.cells ++ Batch13.cells ++ Batch14.cells ++ Batch15.cells ++ Batch16.cells ++ Batch17.cells ++ Batch18.cells ++ Batch19.cells ++ Batch20.cells ++ Batch21.cells ++ Batch22.cells
theorem cells_checked : cells.all SourceCellCertificate.check = true := by
  simp only [cells, List.all_append, Batch00.cells_checked, Batch01.cells_checked, Batch02.cells_checked, Batch03.cells_checked, Batch04.cells_checked, Batch05.cells_checked, Batch06.cells_checked, Batch07.cells_checked, Batch08.cells_checked, Batch09.cells_checked, Batch10.cells_checked, Batch11.cells_checked, Batch12.cells_checked, Batch13.cells_checked, Batch14.cells_checked, Batch15.cells_checked, Batch16.cells_checked, Batch17.cells_checked, Batch18.cells_checked, Batch19.cells_checked, Batch20.cells_checked, Batch21.cells_checked, Batch22.cells_checked, Bool.and_self]

theorem coverage_checked : SourceIntervalCoverage.check SourceCellCertificate.left
    SourceCellCertificate.right (1/32) (1/2) cells = true := by decide +kernel
end SourceCaseOneData

/-- First official numerical source certificate on its full real domain.
All probabilities, unbounded real responses and true retentions are covered. -/
theorem sourceRowValid_22_25_1 :
    SourceRowValid sourceParameters_22_25_1 (22/25) 1 := by
  intro a parentA hs p r z hp hpq hr hr1 hend
  have hpq' : p ≤ (1/2:ℝ) := by norm_num at hpq; exact hpq
  by_cases he : p = 1/2
  · subst p
    have hz : z=a := hend (by norm_num)
    subst z
    exact source_row_22_25_1_leaf hs (by norm_num at hr; exact hr) hr1
  have hpq'' : p < (1/2:ℝ) := lt_of_le_of_ne hpq' he
  by_cases hpo : p ≤ 1/32
  · exact source_row_22_25_1_origin hs hp hpo hr hr1
  obtain ⟨cell,hmem,hl,hh⟩ := SourceIntervalCoverage.check_sound
    SourceCellCertificate.left SourceCellCertificate.right SourceCaseOneData.coverage_checked
    (p:=p) (by norm_num; exact lt_of_not_ge hpo) (by norm_num; exact hpq')
  have hc := (List.all_eq_true.mp SourceCaseOneData.cells_checked) cell hmem
  exact SourceCellCertificate.check_sound hc hs hl hh hpq'' hr hr1

variable {V : Type*} [DecidableEq V]

/-- An unconditional, genuinely heterogeneous forest source bound using the
first official A,C pair. The independent marked set stays fixed. -/
theorem forest_marked_variance_22_25_1 (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) (hB : G.IsIndepSet (B:Set V)) (activity : V→ℝ)
    (hactivity : ∀x∈S, (22/25:ℝ)≤activity x ∧ activity x≤1) :
    heterogeneousVariance G S activity (fun J => ((J∩B).card:ℝ)) ≤
      (14896533/50000000)*heterogeneousMean G S activity (fun J=>(J.card:ℝ)) +
      (3577121/5000000)*heterogeneousMean G S activity (fun J=>((J∩B).card:ℝ)) := by
  simpa only [sourceParameters_22_25_1] using
    forest_independent_count_variance_of_scalar_certificate G hG S B hB activity
      (by norm_num : (0:ℝ)<22/25) hactivity sourceParameters_22_25_1
      sourceParameters_22_25_1_admissible sourceRowValid_22_25_1

/-- Actual availability variance for a maximum marginal independent set;
there is no remaining scalar-certificate or moment hypothesis. -/
theorem IsMaximumMarginalIndependentOn.available_variance_22_25_1
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hzlo : (22/25:ℝ)≤z) (hzhi : z≤1) :
    hardCoreAvailableVariance G S B z ≤
      (1+(3891069/12500000)/(z/(1+z)))*hardCoreAvailableMean G S B z := by
  have h := hB.available_variance_le_of_source_certificate hG
    (by norm_num : (0:ℝ)<22/25) hzlo hzhi sourceParameters_22_25_1
    sourceParameters_22_25_1_admissible (by norm_num [sourceParameters_22_25_1]) sourceRowValid_22_25_1
  norm_num [sourceParameters_22_25_1] at h ⊢
  exact h

#print axioms sourceRowValid_22_25_1
#print axioms forest_marked_variance_22_25_1
#print axioms IsMaximumMarginalIndependentOn.available_variance_22_25_1
end ForestUnimodality
