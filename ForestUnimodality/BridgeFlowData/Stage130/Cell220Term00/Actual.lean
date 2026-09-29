import ForestUnimodality.CorrelatedTwoPhaseData.Stage130Cell220Term00

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell220Term00
def qa : ℚ := (13/23)
def qb : ℚ := (21/37)
def rho : ℚ := (293866307348293569444703934861/1000000000000000000000000000000)
def retention : ℚ := (7/10)
def rate : ℚ := (16087301896897451019379552263/125000000000000000000000000000)
variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) :=
  ForestUnimodality.CorrelatedTwoPhaseData.Stage130Cell220Term00.actual_laplace hB hG hz hq hdensity
#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell220Term00
