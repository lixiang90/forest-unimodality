import ForestUnimodality.BridgeFlowData.Stage99.Cell108Term01.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage99.Cell109Term02
def qa : ℚ := (109/209)
def qb : ℚ := (4583/8778)
def rho : ℚ := (283484719709560213395228539141/1000000000000000000000000000000)
def retention : ℚ := (1/20)
def rate : ℚ := (136776692675249348983649167743/500000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage99.Cell108Term01.retention])
    (by norm_num [rate,BridgeFlowData.Stage99.Cell108Term01.rate])
    (by norm_num [qa,BridgeFlowData.Stage99.Cell108Term01.qa])
    (by norm_num [qb,BridgeFlowData.Stage99.Cell108Term01.qb])
    (by norm_num [rho,BridgeFlowData.Stage99.Cell108Term01.rho])
    (BridgeFlowData.Stage99.Cell108Term01.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage99.Cell109Term02
