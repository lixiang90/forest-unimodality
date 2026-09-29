import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case09
open AffineSource
def parameters : Parameters := ⟨(1240687/10000000), (6494691/5000000), (5753633/10000000), (2570197/2000000), (136299/2500000)⟩
def domain : Domain := ⟨(11/10), (299837/1000000), ⟨2, (1299837/2000000), 16, (1915384718797909047/1000000000000000000), (1915384718797909151/1000000000000000000)⟩, (3668698621004545114592146339284448209/1000000000000000000000000000000000000), (3668698621004545512992167849249540801/1000000000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (12684279109/36960000000) else (586678313/924000000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case09
