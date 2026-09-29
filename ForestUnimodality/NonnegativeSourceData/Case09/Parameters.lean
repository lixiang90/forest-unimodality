import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case09
open NonnegativeSource
def parameters : Parameters :=
  ⟨(21/20),
  (111/250),
  (401053/1000000),
  (36559/40000),
  (289351/1000000),
  ⟨2, (1289351/2000000), 16, (1905368636820525509/1000000000000000000), (1905368636820525601/1000000000000000000)⟩,
  (3630429642179307636446333558919709081/1000000000000000000000000000000000000),
  (3630429642179307987034162733896411201/1000000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case09
