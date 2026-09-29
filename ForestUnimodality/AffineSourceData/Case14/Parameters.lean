import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case14
open AffineSource
def parameters : Parameters := ⟨(197253/1250000), (8245781/5000000), (7371987/10000000), (13676291/10000000), 0⟩
def domain : Domain := ⟨(3/2), (94523/250000), ⟨2, (344523/500000), 16, (995907217796066309/500000000000000000), (1991814435592132881/1000000000000000000)⟩, (991831186458301454321025674324883481/250000000000000000000000000000000000), (3967324745833206864978495818761360161/1000000000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (105537507/200000000) else (99612111/100000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case14
