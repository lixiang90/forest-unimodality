import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case06
open AffineSource
def parameters : Parameters := ⟨(1305921/10000000), (11414743/10000000), (5148533/10000000), (12228413/10000000), (19303/156250)⟩
def domain : Domain := ⟨1, (278467/1000000), ⟨2, (1278467/2000000), 16, (94751389184050287/50000000000000000), (94751389184050291/50000000000000000)⟩, (8977825752307361712071794144782369/2500000000000000000000000000000000), (8977825752307362470082907617184681/2500000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (33852467/120000000) else (20660741/40000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case06
