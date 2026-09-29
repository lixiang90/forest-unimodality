import ForestUnimodality.BridgeFlowData.Stage130.Cell073Term02.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell074Term01
def qa : ℚ := (407/808)
def qb : ℚ := (51/101)
def rho : ℚ := (4334645524664469072387560501/15625000000000000000000000000)
def retention : ℚ := (1/20)
def rate : ℚ := (30124303475181288880305585549/125000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage130.Cell073Term02.retention])
    (by norm_num [rate,BridgeFlowData.Stage130.Cell073Term02.rate])
    (by norm_num [qa,BridgeFlowData.Stage130.Cell073Term02.qa])
    (by norm_num [qb,BridgeFlowData.Stage130.Cell073Term02.qb])
    (by norm_num [rho,BridgeFlowData.Stage130.Cell073Term02.rho])
    (BridgeFlowData.Stage130.Cell073Term02.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell074Term01
