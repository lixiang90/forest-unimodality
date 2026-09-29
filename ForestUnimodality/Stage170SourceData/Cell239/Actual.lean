import ForestUnimodality.Stage170KernelData.Cell239.Budget
import ForestUnimodality.Stage170SourceData.Rates.Batch140_159

namespace ForestUnimodality.Stage170SourceData.Cell239
open Stage170KernelData.Cell239
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
  · exact Window053.window.total_variance Window053.valid hB hG hz hq
  constructor
  · exact Window053.window.available_variance Window053.valid hB hG hz hS hq hrank
  intro i _
  fin_cases i
  · exact Rate151.certificate.actual_laplace Window053.window Window053.valid Rate151.checked hB hG hz hS hq hrank
  · exact Rate154.certificate.actual_laplace Window053.window Window053.valid Rate154.checked hB hG hz hS hq hrank

#print axioms actual_inputs
end ForestUnimodality.Stage170SourceData.Cell239
