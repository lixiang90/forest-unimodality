import ForestUnimodality.BridgeFlowData.Stage80.Cell054Term01.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell055Term01
def qa : ℚ := (9237/19012)
def qb : ℚ := (4631/9506)
def rho : ℚ := (136400698935543597779231127479/500000000000000000000000000000)
def retention : ℚ := (1/10)
def rate : ℚ := (8316643661517113814261543003/31250000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage80.Cell054Term01.retention])
    (by norm_num [rate,BridgeFlowData.Stage80.Cell054Term01.rate])
    (by norm_num [qa,BridgeFlowData.Stage80.Cell054Term01.qa])
    (by norm_num [qb,BridgeFlowData.Stage80.Cell054Term01.qb])
    (by norm_num [rho,BridgeFlowData.Stage80.Cell054Term01.rho])
    (BridgeFlowData.Stage80.Cell054Term01.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell055Term01
