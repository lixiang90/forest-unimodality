import ForestUnimodality.BridgeFlowData.Stage130.Cell209Term01.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell210Term01
def qa : ℚ := (97103/182328)
def qb : ℚ := (57/107)
def rho : ℚ := (3565674460777603109076730067/12500000000000000000000000000)
def retention : ℚ := (3/5)
def rate : ℚ := (81856170281159092252384080797/500000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage130.Cell209Term01.retention])
    (by norm_num [rate,BridgeFlowData.Stage130.Cell209Term01.rate])
    (by norm_num [qa,BridgeFlowData.Stage130.Cell209Term01.qa])
    (by norm_num [qb,BridgeFlowData.Stage130.Cell209Term01.qb])
    (by norm_num [rho,BridgeFlowData.Stage130.Cell209Term01.rho])
    (BridgeFlowData.Stage130.Cell209Term01.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell210Term01
