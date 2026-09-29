import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case15
open AffineSource
def parameters : Parameters := ⟨(2762699/10000000), (11258201/5000000), (9972317/10000000), (15175497/10000000), 0⟩
def domain : Domain := ⟨(9/4), (501363/1000000), ⟨2, (1501363/2000000), 16, (2118443243847817581/1000000000000000000), (423688648769563723/200000000000000000)⟩, (4487801777404463901250905016652691561/1000000000000000000000000000000000000), (179512071096178731287661331757620729/40000000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (23055752813/25740000000) else (3956865829/2340000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case15
