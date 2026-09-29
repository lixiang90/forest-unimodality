import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case15
open NonnegativeSource
def parameters : Parameters :=
  ⟨(3/2),
  (151/250),
  (585277/1000000),
  (6837/6250),
  (37819/100000),
  ⟨2, (137819/200000), 16, (995956018445344459/500000000000000000), (995956018445344591/500000000000000000)⟩,
  (991928390677503312246340211162002681/250000000000000000000000000000000000),
  (991928390677503575178729080732957281/250000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case15
