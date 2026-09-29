import ForestUnimodality.BridgeFlowData.Stage80.Cell103Term00.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell104Term00
def qa : ℚ := (7339/14214)
def qb : ℚ := (107/207)
def rho : ℚ := (283817100007338844195543902303/1000000000000000000000000000000)
def retention : ℚ := (7/10)
def rate : ℚ := (140517020068336089558496102457/1000000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage80.Cell103Term00.retention])
    (by norm_num [rate,BridgeFlowData.Stage80.Cell103Term00.rate])
    (by norm_num [qa,BridgeFlowData.Stage80.Cell103Term00.qa])
    (by norm_num [qb,BridgeFlowData.Stage80.Cell103Term00.qb])
    (by norm_num [rho,BridgeFlowData.Stage80.Cell103Term00.rho])
    (BridgeFlowData.Stage80.Cell103Term00.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell104Term00
