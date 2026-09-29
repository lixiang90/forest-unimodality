import ForestUnimodality.BridgeFlowData.Stage130.Cell194Term00.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell195Term01
def qa : ℚ := (113/213)
def qb : ℚ := (8069/15194)
def rho : ℚ := (11388104638608594711128320207/40000000000000000000000000000)
def retention : ℚ := (3/5)
def rate : ℚ := (81513607253984429225810789303/500000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage130.Cell194Term00.retention])
    (by norm_num [rate,BridgeFlowData.Stage130.Cell194Term00.rate])
    (by norm_num [qa,BridgeFlowData.Stage130.Cell194Term00.qa])
    (by norm_num [qb,BridgeFlowData.Stage130.Cell194Term00.qb])
    (by norm_num [rho,BridgeFlowData.Stage130.Cell194Term00.rho])
    (BridgeFlowData.Stage130.Cell194Term00.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell195Term01
