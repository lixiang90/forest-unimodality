import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case16
open NonnegativeSource
def parameters : Parameters :=
  ⟨(9/4),
  (919/1000),
  (1010327/1000000),
  (1684211/1000000),
  (501461/1000000),
  ⟨2, (1501461/2000000), 16, (2118547050109998777/1000000000000000000), (529636762527499953/250000000000000000)⟩,
  (4488241603529777669046015430941495729/1000000000000000000000000000000000000),
  (280515100220611378402400572415002209/62500000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case16
