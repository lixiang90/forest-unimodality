import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case11
open NonnegativeSource
def parameters : Parameters :=
  ⟨(57/50),
  (19/40),
  (41753/100000),
  (109189/125000),
  (154131/500000),
  ⟨2, (654131/1000000), 16, (961735147607262427/500000000000000000), (192347029521452497/100000000000000000)⟩,
  (924934494143162848365611193245930329/250000000000000000000000000000000000),
  (36997379765726518397075532627535009/10000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case11
