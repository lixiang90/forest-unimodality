import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case12
open AffineSource
def parameters : Parameters := ⟨(6089/50000), (14374921/10000000), (3157579/5000000), (13374929/10000000), (6881/5000000)⟩
def domain : Domain := ⟨(6/5), (80107/250000), ⟨2, (330107/500000), 16, (1935206424267628739/1000000000000000000), (241900803033453609/125000000000000000)⟩, (3745023904526701485991263813938730121/1000000000000000000000000000000000000), (58515998508229718761815197955124881/15625000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (2242780579/5610000000) else (246485501/330000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case12
