import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case04
open NonnegativeSource
def parameters : Parameters :=
  ⟨(9/10),
  (79/200),
  (326577/1000000),
  (793421/1000000),
  (256349/1000000),
  ⟨2, (1256349/2000000), 16, (1874186127770981047/1000000000000000000), (468546531942745277/250000000000000000)⟩,
  (3512573641529184094529081712833216209/1000000000000000000000000000000000000),
  (219535852595574020198736831305806729/62500000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case04
