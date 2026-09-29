import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case10
open NonnegativeSource
def parameters : Parameters :=
  ⟨(11/10),
  (461/1000),
  (433371/1000000),
  (979269/1000000),
  (59987/200000),
  ⟨2, (259987/400000), 16, (1915478574948587057/1000000000000000000), (1915478574948587161/1000000000000000000)⟩,
  (3669058171087069843414250840707921249/1000000000000000000000000000000000000),
  (3669058171087070241833794430014039921/1000000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case10
