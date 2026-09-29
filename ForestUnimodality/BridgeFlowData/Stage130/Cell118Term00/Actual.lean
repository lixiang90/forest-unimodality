import ForestUnimodality.BridgeFlowData.Stage130.Cell117Term00.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell118Term00
def qa : ℚ := (2294/4389)
def qb : ℚ := (1531/2926)
def rho : ℚ := (141294728193629674117055029079/500000000000000000000000000000)
def retention : ℚ := (7/10)
def rate : ℚ := (16380287890207729202771398093/125000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage130.Cell117Term00.retention])
    (by norm_num [rate,BridgeFlowData.Stage130.Cell117Term00.rate])
    (by norm_num [qa,BridgeFlowData.Stage130.Cell117Term00.qa])
    (by norm_num [qb,BridgeFlowData.Stage130.Cell117Term00.qb])
    (by norm_num [rho,BridgeFlowData.Stage130.Cell117Term00.rho])
    (BridgeFlowData.Stage130.Cell117Term00.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell118Term00
