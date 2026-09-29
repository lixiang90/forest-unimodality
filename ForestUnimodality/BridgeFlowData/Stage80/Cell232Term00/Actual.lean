import ForestUnimodality.BridgeFlowData.Stage80.Cell231Term00.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell232Term00
def qa : ℚ := (2/3)
def qb : ℚ := (35/52)
def rho : ℚ := (64803310316680415839760176633/200000000000000000000000000000)
def retention : ℚ := (7/10)
def rate : ℚ := (137374183529187119638413591987/1000000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage80.Cell231Term00.retention])
    (by norm_num [rate,BridgeFlowData.Stage80.Cell231Term00.rate])
    (by norm_num [qa,BridgeFlowData.Stage80.Cell231Term00.qa])
    (by norm_num [qb,BridgeFlowData.Stage80.Cell231Term00.qb])
    (by norm_num [rho,BridgeFlowData.Stage80.Cell231Term00.rho])
    (BridgeFlowData.Stage80.Cell231Term00.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell232Term00
