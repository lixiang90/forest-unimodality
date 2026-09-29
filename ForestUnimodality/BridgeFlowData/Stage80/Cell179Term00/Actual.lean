import ForestUnimodality.BridgeFlowData.Stage80.Cell178Term00.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell179Term00
def qa : ℚ := (29/54)
def qb : ℚ := (2557/4752)
def rho : ℚ := (14540687754300154455099421949/50000000000000000000000000000)
def retention : ℚ := (3/5)
def rate : ℚ := (21457185772644720321925066927/125000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage80.Cell178Term00.retention])
    (by norm_num [rate,BridgeFlowData.Stage80.Cell178Term00.rate])
    (by norm_num [qa,BridgeFlowData.Stage80.Cell178Term00.qa])
    (by norm_num [qb,BridgeFlowData.Stage80.Cell178Term00.qb])
    (by norm_num [rho,BridgeFlowData.Stage80.Cell178Term00.rho])
    (BridgeFlowData.Stage80.Cell178Term00.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell179Term00
