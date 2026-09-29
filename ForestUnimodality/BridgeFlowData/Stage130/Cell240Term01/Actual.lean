import ForestUnimodality.SharedAffineData.EarlyStop20260928.Bounds

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell240Term01
def qa : ℚ := (35/52)
def qb : ℚ := (53/78)
def rho : ℚ := (64136371125126809749987892843/200000000000000000000000000000)
def retention : ℚ := (3/5)
def rate : ℚ := (7751001877292346530475136499/62500000000000000000000000000)
variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) :=
  SharedAffineData.EarlyStop20260928.Stage130Cell240Term01.actual_laplace hB hG hz hS hq hrank
#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell240Term01
