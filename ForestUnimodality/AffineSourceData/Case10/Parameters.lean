import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case10
open AffineSource
def parameters : Parameters := ⟨(76403/625000), (13590599/10000000), (2980747/5000000), (1299813/1000000), (329227/10000000)⟩
def domain : Domain := ⟨(57/50), (77041/250000), ⟨2, (327041/500000), 16, (1923376047479147717/1000000000000000000), (240422005934893479/125000000000000000)⟩, (3699375420016508692934651932706312089/1000000000000000000000000000000000000), (57802740937757955239236607076723441/15625000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (89922136973/243960000000) else (834203311/1219800000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case10
