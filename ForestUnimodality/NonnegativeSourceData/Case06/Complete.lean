import ForestUnimodality.NonnegativeSourceData.Case06.Batch00
import ForestUnimodality.NonnegativeSourceData.Case06.Batch01
import ForestUnimodality.NonnegativeSourceData.Case06.Batch02
import ForestUnimodality.NonnegativeSourceData.Case06.Batch03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case06
open NonnegativeSource
def cells : List Cell := Batch00.cells ++ Batch01.cells ++ Batch02.cells ++ Batch03.cells
theorem cells_checked : cells.all (fun c=>c.check parameters)=true := by
  simp only [cells,List.all_append,Batch00.cells_checked, Batch01.cells_checked, Batch02.cells_checked, Batch03.cells_checked,Bool.and_self]
theorem coverage_checked : SourceIntervalCoverage.check Cell.left Cell.right 0 parameters.q cells=true := by decide +kernel

theorem source_valid : NonnegativeSourceRowValid parameters.b parameters.A parameters.u parameters.v :=
  sourceRowValid_of_cells parameters (Parameters.check_sound parameters_checked) cells cells_checked coverage_checked

variable {V : Type*} [DecidableEq V]

/-- Actual forest bound, including zero activities and arbitrary nonnegative marks. -/
theorem forest_variance (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (activity a : V→ℝ)
    (hactivity : ∀x∈S, 0≤activity x ∧ activity x≤(1:ℝ))
    (ha : ∀x∈S, 0≤a x) :
    heterogeneousVariance G S activity (markedSum a)≤(427/1000)*(∑x∈S, a x^2) := by
  have hact : ∀x∈S, 0≤activity x ∧ activity x≤(parameters.b:ℝ) := by
    norm_num [parameters]
    exact hactivity
  have hv := Parameters.check_sound parameters_checked
  have h := forest_nonnegative_source_variance G hG S activity a hv.b_pos hact ha
    hv.u_nonneg hv.v_nonneg source_valid
  norm_num [parameters] at h ⊢
  exact h

#print axioms source_valid
#print axioms forest_variance
end ForestUnimodality.NonnegativeSourceData.Case06
