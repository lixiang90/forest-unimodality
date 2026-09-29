import ForestUnimodality.Stage170KernelData.Cell166.Budget
import ForestUnimodality.Stage170SourceData.Rates.Batch100_119

namespace ForestUnimodality.Stage170SourceData.Cell166
open Stage170KernelData.Cell166
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
  · exact Window038.window.total_variance Window038.valid hB hG hz hq
  constructor
  · exact Window038.window.available_variance Window038.valid hB hG hz hS hq hrank
  intro i _
  fin_cases i
  · exact Rate107.certificate.actual_laplace Window038.window Window038.valid Rate107.checked hB hG hz hS hq hrank
  · exact Rate106.certificate.actual_laplace Window038.window Window038.valid Rate106.checked hB hG hz hS hq hrank

#print axioms actual_inputs
end ForestUnimodality.Stage170SourceData.Cell166
