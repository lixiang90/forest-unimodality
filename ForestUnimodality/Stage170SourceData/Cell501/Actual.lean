import ForestUnimodality.Stage170KernelData.Cell501.Budget
import ForestUnimodality.Stage170SourceData.Rates.Batch340_359
import ForestUnimodality.Stage170SourceData.Rates.Batch360_379

namespace ForestUnimodality.Stage170SourceData.Cell501
open Stage170KernelData.Cell501
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
  · exact Window122.window.total_variance Window122.valid hB hG hz hq
  constructor
  · exact Window122.window.available_variance Window122.valid hB hG hz hS hq hrank
  intro i _
  fin_cases i
  · exact Rate359.certificate.actual_laplace Window122.window Window122.valid Rate359.checked hB hG hz hS hq hrank
  · exact Rate360.certificate.actual_laplace Window122.window Window122.valid Rate360.checked hB hG hz hS hq hrank

#print axioms actual_inputs
end ForestUnimodality.Stage170SourceData.Cell501
