import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case08
open AffineSource
def parameters : Parameters := ⟨(1280313/10000000), (12161069/10000000), (2717499/5000000), (12495141/10000000), (459297/5000000)⟩
def domain : Domain := ⟨(21/20), (289253/1000000), ⟨2, (1289253/2000000), 16, (119079704752792437/62500000000000000), (1905275276044679083/1000000000000000000)⟩, (14179976084012217709493749204398969/3906250000000000000000000000000000), (3630073877507128080390500036457720889/1000000000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (55534491199/177940000000) else (1647256781/2870000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case08
