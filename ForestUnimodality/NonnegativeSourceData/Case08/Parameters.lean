import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case08
open NonnegativeSource
def parameters : Parameters :=
  ⟨(103/100),
  (11/25),
  (39/100),
  (89/100),
  (57/200),
  ⟨2, (257/400), 16, (1901228012947802029/1000000000000000000), (380245602589560423/200000000000000000)⟩,
  (3614667957217447679628801382176516841/1000000000000000000000000000000000000),
  (144586718288697920265600784367938929/40000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case08
