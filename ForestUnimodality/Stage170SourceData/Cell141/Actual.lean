import ForestUnimodality.Stage170KernelData.Cell141.Budget
import ForestUnimodality.Stage170SourceData.Rates.Batch080_099

namespace ForestUnimodality.Stage170SourceData.Cell141
open Stage170KernelData.Cell141
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
  · exact Window033.window.total_variance Window033.valid hB hG hz hq
  constructor
  · exact Window033.window.available_variance Window033.valid hB hG hz hS hq hrank
  intro i _
  fin_cases i
  · exact Rate092.certificate.actual_laplace Window033.window Window033.valid Rate092.checked hB hG hz hS hq hrank
  · exact Rate091.certificate.actual_laplace Window033.window Window033.valid Rate091.checked hB hG hz hS hq hrank

#print axioms actual_inputs
end ForestUnimodality.Stage170SourceData.Cell141
