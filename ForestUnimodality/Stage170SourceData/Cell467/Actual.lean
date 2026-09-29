import ForestUnimodality.Stage170KernelData.Cell467.Budget
import ForestUnimodality.Stage170SourceData.Rates.Batch280_299

namespace ForestUnimodality.Stage170SourceData.Cell467
open Stage170KernelData.Cell467
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
  · exact Window088.window.total_variance Window088.valid hB hG hz hq
  constructor
  · exact Window088.window.available_variance Window088.valid hB hG hz hS hq hrank
  intro i _
  fin_cases i
  · exact Rate292.certificate.actual_laplace Window088.window Window088.valid Rate292.checked hB hG hz hS hq hrank
  · exact Rate293.certificate.actual_laplace Window088.window Window088.valid Rate293.checked hB hG hz hS hq hrank

#print axioms actual_inputs
end ForestUnimodality.Stage170SourceData.Cell467
