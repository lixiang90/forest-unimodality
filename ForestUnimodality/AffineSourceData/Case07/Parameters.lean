import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case07
open AffineSource
def parameters : Parameters := ⟨(645861/5000000), (11855957/10000000), (5417567/10000000), (2542307/2000000), (92959/1000000)⟩
def domain : Domain := ⟨(103/100), (71241/250000), ⟨2, (321241/500000), 16, (950596895575783029/500000000000000000), (380238758230313229/200000000000000000)⟩, (903634457878316144453716006484414841/250000000000000000000000000000000000), (144581513260530596344903347452406441/40000000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (2355940593271/7997692500000) else (32453815017/59740000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case07
