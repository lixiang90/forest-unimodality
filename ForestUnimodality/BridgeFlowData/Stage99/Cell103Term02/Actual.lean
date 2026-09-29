import ForestUnimodality.BridgeFlowData.Stage99.Cell102Term01.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage99.Cell103Term02
def qa : ℚ := (22597/43472)
def qb : ℚ := (11311/21736)
def rho : ℚ := (283015441161095009944747266327/1000000000000000000000000000000)
def retention : ℚ := (1/20)
def rate : ℚ := (68103921551285512764777048459/250000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage99.Cell102Term01.retention])
    (by norm_num [rate,BridgeFlowData.Stage99.Cell102Term01.rate])
    (by norm_num [qa,BridgeFlowData.Stage99.Cell102Term01.qa])
    (by norm_num [qb,BridgeFlowData.Stage99.Cell102Term01.qb])
    (by norm_num [rho,BridgeFlowData.Stage99.Cell102Term01.rho])
    (BridgeFlowData.Stage99.Cell102Term01.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage99.Cell103Term02
