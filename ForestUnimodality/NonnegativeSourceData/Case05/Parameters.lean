import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case05
open NonnegativeSource
def parameters : Parameters :=
  ⟨(24/25),
  (207/500),
  (346301/1000000),
  (32063/40000),
  (33723/125000),
  ⟨2, (158723/250000), 16, (471704588518044277/250000000000000000), (1886818354072177179/1000000000000000000)⟩,
  (222505218828977468764455624932452729/62500000000000000000000000000000000),
  (3560083501263639768159496277168398041/1000000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case05
