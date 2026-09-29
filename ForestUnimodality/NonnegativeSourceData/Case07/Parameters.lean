import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case07
open NonnegativeSource
def parameters : Parameters :=
  ⟨(101/100),
  (43/100),
  (19/50),
  (22/25),
  (281/1000),
  ⟨2, (1281/2000), 16, (1897429356844228619/1000000000000000000), (1897429356844228701/1000000000000000000)⟩,
  (3600238164214303066444600689138647161/1000000000000000000000000000000000000),
  (3600238164214303377623015211592147401/1000000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case07
