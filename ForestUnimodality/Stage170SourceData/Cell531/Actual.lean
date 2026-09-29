import ForestUnimodality.Stage170KernelData.Cell531.Budget
import ForestUnimodality.Stage170SourceData.Rates.Batch140_159
import ForestUnimodality.Stage170SourceData.Rates.Batch400_416

namespace ForestUnimodality.Stage170SourceData.Cell531
open Stage170KernelData.Cell531
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
  · exact Window052.window.total_variance Window052.valid hB hG hz hq
  constructor
  · exact Window052.window.available_variance Window052.valid hB hG hz hS hq hrank
  intro i _
  fin_cases i
  · exact Rate148.certificate.actual_laplace Window052.window Window052.valid Rate148.checked hB hG hz hS hq hrank
  · exact Rate414.certificate.actual_laplace Window052.window Window052.valid Rate414.checked hB hG hz hS hq hrank
  · exact Rate149.certificate.actual_laplace Window052.window Window052.valid Rate149.checked hB hG hz hS hq hrank

#print axioms actual_inputs
end ForestUnimodality.Stage170SourceData.Cell531
