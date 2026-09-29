import ForestUnimodality.Stage170KernelData.Cell292.Budget
import ForestUnimodality.Stage170SourceData.Rates.Batch180_199

namespace ForestUnimodality.Stage170SourceData.Cell292
open Stage170KernelData.Cell292
variable {V : Type*} [DecidableEq V]

theorem actual_inputs {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(R*vmax:ℚ))*hardCoreAvailableMean G S B z+0) ∧
    (hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z) ∧
    (∀i∈row.terms,hardCoreLayerLaplace G S B z (row.retention i)≤
      Real.exp (-(rate i:ℝ)*hardCoreAvailableMean G S B z)) := by
  constructor
  · exact Window065.window.total_variance Window065.valid hB hG hz hq
  constructor
  · exact Window065.window.available_variance Window065.valid hB hG hz hS hq hrank
  intro i _
  fin_cases i
  · exact Rate183.certificate.actual_laplace Window065.window Window065.valid Rate183.checked hB hG hz hS hq hrank
  · exact Rate182.certificate.actual_laplace Window065.window Window065.valid Rate182.checked hB hG hz hS hq hrank

#print axioms actual_inputs
end ForestUnimodality.Stage170SourceData.Cell292
