import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case03
open AffineSource
def parameters : Parameters := ⟨(863869/10000000), (753433/625000), (4656899/10000000), (12113439/10000000), (127551/2500000)⟩
def domain : Domain := ⟨(17/20), (244801/1000000), ⟨2, (1244801/2000000), 16, (1863395758842721453/1000000000000000000), (372679151768544301/200000000000000000)⟩, (3472243754073041726101772195346431209/1000000000000000000000000000000000000), (138889750162921676795797244599578601/40000000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (93829291381/339660000000) else (1243567523/2516000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case03
