import ForestUnimodality.BridgeFlowData.Stage130.Cell049Term01.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell050Term02
def qa : ℚ := (9237/19012)
def qb : ℚ := (4631/9506)
def rho : ℚ := (125674035996535671754898776659/500000000000000000000000000000)
def retention : ℚ := (1/1000)
def rate : ℚ := (7561718281040784954940090031/31250000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage130.Cell049Term01.retention])
    (by norm_num [rate,BridgeFlowData.Stage130.Cell049Term01.rate])
    (by norm_num [qa,BridgeFlowData.Stage130.Cell049Term01.qa])
    (by norm_num [qb,BridgeFlowData.Stage130.Cell049Term01.qb])
    (by norm_num [rho,BridgeFlowData.Stage130.Cell049Term01.rho])
    (BridgeFlowData.Stage130.Cell049Term01.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell050Term02
