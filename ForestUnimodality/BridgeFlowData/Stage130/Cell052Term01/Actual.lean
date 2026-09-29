import ForestUnimodality.BridgeFlowData.Stage130.Cell051Term01.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell052Term01
def qa : ℚ := (4631/9506)
def qb : ℚ := (9287/19012)
def rho : ℚ := (253736986180090693154826171453/1000000000000000000000000000000)
def retention : ℚ := (3/5)
def rate : ℚ := (390222443169049282954229461/2500000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage130.Cell051Term01.retention])
    (by norm_num [rate,BridgeFlowData.Stage130.Cell051Term01.rate])
    (by norm_num [qa,BridgeFlowData.Stage130.Cell051Term01.qa])
    (by norm_num [qb,BridgeFlowData.Stage130.Cell051Term01.qb])
    (by norm_num [rho,BridgeFlowData.Stage130.Cell051Term01.rho])
    (BridgeFlowData.Stage130.Cell051Term01.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell052Term01
