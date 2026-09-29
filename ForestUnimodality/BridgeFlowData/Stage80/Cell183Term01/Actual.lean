import ForestUnimodality.BridgeFlowData.Stage80.Cell182Term01.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell183Term01
def qa : ℚ := (2557/4752)
def qb : ℚ := (427/792)
def rho : ℚ := (291098503763917921339997039819/1000000000000000000000000000000)
def retention : ℚ := (1/5)
def rate : ℚ := (222149204557596654274635024741/1000000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage80.Cell182Term01.retention])
    (by norm_num [rate,BridgeFlowData.Stage80.Cell182Term01.rate])
    (by norm_num [qa,BridgeFlowData.Stage80.Cell182Term01.qa])
    (by norm_num [qb,BridgeFlowData.Stage80.Cell182Term01.qb])
    (by norm_num [rho,BridgeFlowData.Stage80.Cell182Term01.rho])
    (BridgeFlowData.Stage80.Cell182Term01.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell183Term01
