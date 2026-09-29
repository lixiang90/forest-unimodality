import ForestUnimodality.SharedAffineData.EarlyStop20260928.Bounds

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell239Term01
def qa : ℚ := (2/3)
def qb : ℚ := (35/52)
def rho : ℚ := (159575572952128233929977158889/500000000000000000000000000000)
def retention : ℚ := (3/5)
def rate : ℚ := (61304787699704703640566705149/500000000000000000000000000000)
variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) :=
  SharedAffineData.EarlyStop20260928.Stage130Cell239Term01.actual_laplace hB hG hz hS hq hrank
#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell239Term01
