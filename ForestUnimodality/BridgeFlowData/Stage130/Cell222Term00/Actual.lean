import ForestUnimodality.SharedAffineData.Screen20260928.Bounds

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell222Term00
def qa : ℚ := (53/93)
def qb : ℚ := (107/187)
def rho : ℚ := (295079132590324090026885569447/1000000000000000000000000000000)
def retention : ℚ := (7/10)
def rate : ℚ := (129826796295382216493053551641/1000000000000000000000000000000)
variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) :=
  SharedAffineData.Screen20260928.Stage130Cell222Term00.actual_laplace hB hG hz hS hq hrank
#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell222Term00
