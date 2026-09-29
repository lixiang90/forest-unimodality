import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case01
open AffineSource
def parameters : Parameters := ⟨(1273553/10000000), (59373/100000), (11329/50000), (1040917/1250000), (3913437/10000000)⟩
def domain : Domain := ⟨(1/2), (157187/1000000), ⟨2, (1157187/2000000), 16, (1783528133477611577/1000000000000000000), (891764066738805797/500000000000000000)⟩, (3180972602906133057680104300484426929/1000000000000000000000000000000000000), (795243150726533279580015209680805209/250000000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (4399367/60000000) else (3609377/30000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case01
