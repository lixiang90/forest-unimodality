import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case06
open NonnegativeSource
def parameters : Parameters :=
  ⟨1,
  (427/1000),
  (370029/1000000),
  (850727/1000000),
  (55713/200000),
  ⟨2, (255713/400000), 16, (947560321158712061/500000000000000000), (947560321158712101/500000000000000000)⟩,
  (897870562234401543960652680306867721/250000000000000000000000000000000000),
  (897870562234401619765478373003834201/250000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case06
