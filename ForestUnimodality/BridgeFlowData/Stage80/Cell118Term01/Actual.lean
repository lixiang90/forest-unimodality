import ForestUnimodality.BridgeFlowData.Stage80.Cell117Term02.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell118Term01
def qa : ℚ := (22647/43472)
def qb : ℚ := (109/209)
def rho : ℚ := (71367569773980750247702571681/250000000000000000000000000000)
def retention : ℚ := (1/20)
def rate : ℚ := (68326549772232690269686945601/250000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage80.Cell117Term02.retention])
    (by norm_num [rate,BridgeFlowData.Stage80.Cell117Term02.rate])
    (by norm_num [qa,BridgeFlowData.Stage80.Cell117Term02.qa])
    (by norm_num [qb,BridgeFlowData.Stage80.Cell117Term02.qb])
    (by norm_num [rho,BridgeFlowData.Stage80.Cell117Term02.rho])
    (BridgeFlowData.Stage80.Cell117Term02.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell118Term01
