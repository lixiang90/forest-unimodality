import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case02
open NonnegativeSource
def parameters : Parameters :=
  ⟨(7/10),
  (83/250),
  (230741/1000000),
  (305797/500000),
  (209057/1000000),
  ⟨2, (1209057/2000000), 16, (457597244248048683/250000000000000000), (915194488496097383/500000000000000000)⟩,
  (209395237943408323498787453138034489/62500000000000000000000000000000000),
  (837580951773633325111762421419448689/250000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case02
