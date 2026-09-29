import ForestUnimodality.SharedAffineData.Screen20260928.Bounds

namespace ForestUnimodality.BridgeFlowData.Stage130.Cell221Term00
def qa : ℚ := (21/37)
def qb : ℚ := (53/93)
def rho : ℚ := (294476622247363154272782452191/1000000000000000000000000000000)
def retention : ℚ := (7/10)
def rate : ℚ := (64632793674250195035478535161/500000000000000000000000000000)
variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) :=
  SharedAffineData.Screen20260928.Stage130Cell221Term00.actual_laplace hB hG hz hS hq hrank
#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage130.Cell221Term00
