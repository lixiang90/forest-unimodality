import ForestUnimodality.AffineSourceData.Case01.Batch00
import ForestUnimodality.AffineSourceData.Case01.Batch01
import ForestUnimodality.AffineSourceData.Case01.Batch02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case01
open AffineSource
def cells : List Cell := Batch00.cells ++ Batch01.cells ++ Batch02.cells
theorem cells_checked : cells.all (fun c=>c.check parameters domain)=true := by
  simp only [cells,List.all_append,Batch00.cells_checked, Batch01.cells_checked, Batch02.cells_checked,Bool.and_self]
theorem coverage_checked : SourceIntervalCoverage.check Cell.left Cell.right 0 (probabilityCap domain) cells=true := by decide +kernel
theorem source_valid : AffineSourceRowValid parameters.toReal domain.b :=
  sourceRowValid_of_checked parameters domain leaf cells parameters_checked domain_checked leaf_checked cells_checked coverage_checked
#print axioms coverage_checked
#print axioms source_valid
end ForestUnimodality.AffineSourceData.Case01
