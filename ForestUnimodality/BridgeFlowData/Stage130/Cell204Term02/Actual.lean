import ForestUnimodality.BridgeFlowData.Stage130.Cell203Term02.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell204Term02
def qa : ℚ := (24257/45582)
def qb : ℚ := (32351/60776)
def rho : ℚ := (285143773966615963161816456887/1000000000000000000000000000000)
def retention : ℚ := (1/20)
def rate : ℚ := (120197081477599202116636145047/500000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage130.Cell203Term02.retention])
    (by norm_num [rate,BridgeFlowData.Stage130.Cell203Term02.rate])
    (by norm_num [qa,BridgeFlowData.Stage130.Cell203Term02.qa])
    (by norm_num [qb,BridgeFlowData.Stage130.Cell203Term02.qb])
    (by norm_num [rho,BridgeFlowData.Stage130.Cell203Term02.rho])
    (BridgeFlowData.Stage130.Cell203Term02.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell204Term02
