import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case03
open NonnegativeSource
def parameters : Parameters :=
  ⟨(17/20),
  (379/1000),
  (302687/1000000),
  (752093/1000000),
  (244899/1000000),
  ⟨2, (1244899/2000000), 16, (1863487067471947893/1000000000000000000), (372697413494389589/200000000000000000)⟩,
  (3472584050635200079029534475707139449/1000000000000000000000000000000000000),
  (138903362025408010913287579711588921/40000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case03
