import ForestUnimodality.BridgeFlowData.Stage130.Cell119Term00.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell120Term00
def qa : ℚ := (1531/2926)
def qb : ℚ := (11/21)
def rho : ℚ := (282743397378350725744443786739/1000000000000000000000000000000)
def retention : ℚ := (7/10)
def rate : ℚ := (32797675338533206383222819069/250000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage130.Cell119Term00.retention])
    (by norm_num [rate,BridgeFlowData.Stage130.Cell119Term00.rate])
    (by norm_num [qa,BridgeFlowData.Stage130.Cell119Term00.qa])
    (by norm_num [qb,BridgeFlowData.Stage130.Cell119Term00.qb])
    (by norm_num [rho,BridgeFlowData.Stage130.Cell119Term00.rho])
    (BridgeFlowData.Stage130.Cell119Term00.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell120Term00
