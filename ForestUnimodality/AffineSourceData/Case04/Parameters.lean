import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case04
open AffineSource
def parameters : Parameters := ⟨(837913/10000000), (12800017/10000000), (4977213/10000000), (1559709/1250000), (160269/10000000)⟩
def domain : Domain := ⟨(9/10), (256251/1000000), ⟨2, (1256251/2000000), 16, (1874094294900643967/1000000000000000000), (468523573725161007/250000000000000000)⟩, (3512229426179141875771608151293497089/1000000000000000000000000000000000000), (219514339136196381525694508073254049/62500000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (154108691/504000000) else (1883526407/3420000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case04
