import ForestUnimodality.BridgeFlowData.Stage80.Cell075Term02.Actual
import ForestUnimodality.LaplaceBoundTransfer

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell076Term02
def qa : ℚ := (3193/6468)
def qb : ℚ := (49/99)
def rho : ℚ := (275650285795017466046030782879/1000000000000000000000000000000)
def retention : ℚ := (1/10)
def rate : ℚ := (272909199363842534270480855591/1000000000000000000000000000000)

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  exact hardCoreLayerLaplace_restrict G S B hz.le
    (by norm_num [retention])
    (by norm_num [retention,BridgeFlowData.Stage80.Cell075Term02.retention])
    (by norm_num [rate,BridgeFlowData.Stage80.Cell075Term02.rate])
    (by norm_num [qa,BridgeFlowData.Stage80.Cell075Term02.qa])
    (by norm_num [qb,BridgeFlowData.Stage80.Cell075Term02.qb])
    (by norm_num [rho,BridgeFlowData.Stage80.Cell075Term02.rho])
    (BridgeFlowData.Stage80.Cell075Term02.actual_laplace hB hG hz) hq hdensity

#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell076Term02
