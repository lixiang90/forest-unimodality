import ForestUnimodality.BridgeFlowData.Stage130.Cell145Term01.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell147Term03
def qa : ℚ := (94503/178928)
def qb : ℚ := (28/53)
def rho : ℚ := (142035101476242846269340211681/500000000000000000000000000000)
def retention : ℚ := (1/100)
def rate : ℚ := (47914352273274348479250454603/200000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage130.Cell145Term01.retention])
    (by norm_num [rate,BridgeFlowData.Stage130.Cell145Term01.rate])
    (by norm_num [qa,BridgeFlowData.Stage130.Cell145Term01.qa])
    (by norm_num [qb,BridgeFlowData.Stage130.Cell145Term01.qb])
    (by norm_num [rho,BridgeFlowData.Stage130.Cell145Term01.rho])
    (BridgeFlowData.Stage130.Cell145Term01.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell147Term03
