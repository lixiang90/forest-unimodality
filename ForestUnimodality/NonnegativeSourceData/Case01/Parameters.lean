import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case01
open NonnegativeSource
def parameters : Parameters :=
  ⟨(1/2),
  (269/1000),
  (34637/250000),
  (390499/1000000),
  (31457/200000),
  ⟨2, (231457/400000), 16, (445903882124328119/250000000000000000), (1783615528497312493/1000000000000000000)⟩,
  (198830272093546705823173397174078161/62500000000000000000000000000000000),
  (3181284353496747353813702323693875049/1000000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case01
