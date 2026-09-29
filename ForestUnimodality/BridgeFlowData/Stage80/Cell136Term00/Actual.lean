import ForestUnimodality.BridgeFlowData.Stage80.Cell137Term00.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell136Term00
def qa : ℚ := (2326/4431)
def qb : ℚ := (4657/8862)
def rho : ℚ := (14344325839341623113989393853/50000000000000000000000000000)
def retention : ℚ := (7/10)
def rate : ℚ := (143500979368376173714454089903/1000000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage80.Cell137Term00.retention])
    (by norm_num [rate,BridgeFlowData.Stage80.Cell137Term00.rate])
    (by norm_num [qa,BridgeFlowData.Stage80.Cell137Term00.qa])
    (by norm_num [qb,BridgeFlowData.Stage80.Cell137Term00.qb])
    (by norm_num [rho,BridgeFlowData.Stage80.Cell137Term00.rho])
    (BridgeFlowData.Stage80.Cell137Term00.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell136Term00
