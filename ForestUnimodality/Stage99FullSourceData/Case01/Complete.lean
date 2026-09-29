import ForestUnimodality.Stage99FullSourceData.Case01.Batch00
import ForestUnimodality.Stage99FullSourceData.Case01.Batch01
import ForestUnimodality.Stage99FullSourceData.Case01.Batch02
import ForestUnimodality.FullSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.Stage99FullSourceData.Case01
open ParametricSource (Domain)
open FullParametricSource
def cells : List Cell := Batch00.cells ++ Batch01.cells ++ Batch02.cells
theorem cells_checked : cells.all (Cell.check parameters domain)=true := by
  simp only [cells,List.all_append,Batch00.cells_checked, Batch01.cells_checked, Batch02.cells_checked,Bool.and_self]
theorem coverage_checked : SourceIntervalCoverage.check Cell.left Cell.right origin.delta
    (domain.b/(1+domain.b)) cells=true := by decide +kernel

theorem source_valid : FullSourceRowValid parameters.toReal domain.lower domain.b :=
  sourceRowValid_of_checked parameters domain origin leaf cells parameters_checked domain_checked
    origin_checked leaf_checked cells_checked coverage_checked

variable {V : Type*} [DecidableEq V]
theorem forest_full_variance (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (activity : V→ℝ) (hactivity : ∀x∈S, ((17/20):ℝ)≤activity x ∧ activity x≤1) :
    heterogeneousVariance G S activity (fun J=>(J.card:ℝ)) ≤
      (352048071/500000000)*heterogeneousMean G S activity (fun J=>(J.card:ℝ)) := by
  have hact : ∀x∈S, (domain.lower:ℝ)≤activity x ∧ activity x≤(domain.b:ℝ) := by
    norm_num [domain]
    exact hactivity
  have h := forest_full_count_variance_of_scalar_certificate G hG S activity
    (Domain.check_sound domain_checked).lower_pos hact parameters.toReal
    (parameters.admissible_sound parameters_checked) source_valid
  norm_num [parameters,RationalSourceParameters.toReal] at h ⊢
  exact h
#print axioms source_valid
#print axioms forest_full_variance
end ForestUnimodality.Stage99FullSourceData.Case01
