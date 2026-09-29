import ForestUnimodality.BridgeFlowData.Stage130.Cell132Term00.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell134Term01
def qa : ℚ := (23557/44732)
def qb : ℚ := (11791/22366)
def rho : ℚ := (141828292645637498352029389169/500000000000000000000000000000)
def retention : ℚ := (3/5)
def rate : ℚ := (40444484420403015457596342947/250000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage130.Cell132Term00.retention])
    (by norm_num [rate,BridgeFlowData.Stage130.Cell132Term00.rate])
    (by norm_num [qa,BridgeFlowData.Stage130.Cell132Term00.qa])
    (by norm_num [qb,BridgeFlowData.Stage130.Cell132Term00.qb])
    (by norm_num [rho,BridgeFlowData.Stage130.Cell132Term00.rho])
    (BridgeFlowData.Stage130.Cell132Term00.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell134Term01
