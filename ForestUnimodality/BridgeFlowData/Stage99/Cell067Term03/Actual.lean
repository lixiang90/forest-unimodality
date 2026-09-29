import ForestUnimodality.BridgeFlowData.Stage99.Cell066Term02.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage99.Cell067Term03
def qa : ℚ := (407/808)
def qb : ℚ := (51/101)
def rho : ℚ := (27859997491663628293951163033/100000000000000000000000000000)
def retention : ℚ := (1/100)
def rate : ℚ := (17049197005603447824902499771/62500000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage99.Cell066Term02.retention])
    (by norm_num [rate,BridgeFlowData.Stage99.Cell066Term02.rate])
    (by norm_num [qa,BridgeFlowData.Stage99.Cell066Term02.qa])
    (by norm_num [qb,BridgeFlowData.Stage99.Cell066Term02.qb])
    (by norm_num [rho,BridgeFlowData.Stage99.Cell066Term02.rho])
    (BridgeFlowData.Stage99.Cell066Term02.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage99.Cell067Term03
