import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case11
open AffineSource
def parameters : Parameters := ⟨(611627/5000000), (6919207/5000000), (6154413/10000000), (13352763/10000000), (134517/10000000)⟩
def domain : Domain := ⟨(29/25), (312281/1000000), ⟨2, (1312281/2000000), 16, (1927339394948735313/1000000000000000000), (963669697474367717/500000000000000000)⟩, (3714637143321357123347739338133207969/1000000000000000000000000000000000000), (928659285830339397440968228931792089/250000000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (324550062059/866520000000) else (21876169793/31320000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case11
