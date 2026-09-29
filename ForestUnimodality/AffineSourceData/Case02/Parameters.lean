import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case02
open AffineSource
def parameters : Parameters := ⟨(487813/5000000), (4846289/5000000), (3647771/10000000), (5375517/5000000), (86487/500000)⟩
def domain : Domain := ⟨(7/10), (208959/1000000), ⟨2, (1208959/2000000), 16, (1830299290129668191/1000000000000000000), (73211971605186729/40000000000000000)⟩, (3349995491449167295862582619757212481/1000000000000000000000000000000000000), (5359992786318667872516694957719441/1600000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (2677155001/14280000000) else (781316673/2380000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case02
