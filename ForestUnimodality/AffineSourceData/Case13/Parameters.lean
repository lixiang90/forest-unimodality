import ForestUnimodality.AffineSourceAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.AffineSourceData.Case13
open AffineSource
def parameters : Parameters := ⟨(262141/2000000), (1517789/1000000), (3319991/5000000), (2667927/2000000), 0⟩
def domain : Domain := ⟨(13/10), (3403/10000), ⟨2, (13403/20000), 16, (1954530478220303877/1000000000000000000), (977265239110152023/500000000000000000)⟩, (3820189390292089768084660210221231129/1000000000000000000000000000000000000), (955047347573022607178990462170992529/250000000000000000000000000000000000)⟩
def leaf : BernsteinCertificate.Certificate := ⟨1, (fun i=>if i.val=0 then (2675859697/5980000000) else (626818979/747500000))⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
theorem domain_checked : domain.check=true := by decide +kernel
theorem leaf_checked : leafCheck parameters domain leaf=true := by decide +kernel
#print axioms parameters_checked
#print axioms domain_checked
#print axioms leaf_checked
end ForestUnimodality.AffineSourceData.Case13
