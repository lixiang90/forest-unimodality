import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case12
open NonnegativeSource
def parameters : Parameters :=
  ⟨(29/25),
  (241/500),
  (214961/500000),
  (448681/500000),
  (312379/1000000),
  ⟨2, (1312379/2000000), 16, (240929229611612067/125000000000000000), (1927433836892896657/1000000000000000000)⟩,
  (58046893681244888872882006500012489/15625000000000000000000000000000000),
  (3715001195599673354303436944081775649/1000000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case12
