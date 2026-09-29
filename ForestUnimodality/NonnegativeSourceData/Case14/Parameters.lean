import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case14
open NonnegativeSource
def parameters : Parameters :=
  ⟨(13/10),
  (531/1000),
  (130297/250000),
  (214151/200000),
  (170199/500000),
  ⟨2, (670199/1000000), 16, (488656563140047209/250000000000000000), (390925250512037801/200000000000000000)⟩,
  (238785236699842944634978554748689681/62500000000000000000000000000000000),
  (152822551487899510992933209652915601/40000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case14
