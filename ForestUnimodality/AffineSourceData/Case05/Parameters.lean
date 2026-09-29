import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case05
open AffineSource
def parameters : Parameters := ⟨(824419/10000000), (6800349/5000000), (5200899/10000000), (6189123/5000000), 0⟩
def domain : Domain := ⟨(24/25), (134843/500000), ⟨2, (634843/1000000), 16, (235840737779739501/125000000000000000), (23584073777973951/12500000000000000)⟩, (55620853596491846775698163419729001/15625000000000000000000000000000000), (556208535964918510208314434550401/156250000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (297081936163/858480000000) else (1471090511/2352000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case05
