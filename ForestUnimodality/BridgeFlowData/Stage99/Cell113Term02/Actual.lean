import ForestUnimodality.BridgeFlowData.Stage99.Cell112Term01.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage99.Cell113Term02
def qa : ℚ := (2294/4389)
def qb : ℚ := (1531/2926)
def rho : ℚ := (70948541788570732648746558673/250000000000000000000000000000)
def retention : ℚ := (1/20)
def rate : ℚ := (137521275419541156244825012453/500000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage99.Cell112Term01.retention])
    (by norm_num [rate,BridgeFlowData.Stage99.Cell112Term01.rate])
    (by norm_num [qa,BridgeFlowData.Stage99.Cell112Term01.qa])
    (by norm_num [qb,BridgeFlowData.Stage99.Cell112Term01.qb])
    (by norm_num [rho,BridgeFlowData.Stage99.Cell112Term01.rho])
    (BridgeFlowData.Stage99.Cell112Term01.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage99.Cell113Term02
