import ForestUnimodality.Stage130KernelData.Cell018.Budget
import ForestUnimodality.BridgeFlowData.Stage130.Cell018Term02.Actual
import ForestUnimodality.Stage170SourceData.Rates.Batch040_059
import ForestUnimodality.Stage170SourceData.Rates.Batch220_239
import ForestUnimodality.Stage170SourceData.Windows.Batch000_019

namespace ForestUnimodality.Stage130SourceData.Cell018
open Stage130KernelData.Cell018
variable {V : Type*} [DecidableEq V]

theorem actual_inputs {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept) ∧
    (hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z) ∧
    (∀i∈row.terms,hardCoreLayerLaplace G S B z (row.retention i)≤
      Real.exp (-(rate i:ℝ)*hardCoreAvailableMean G S B z)) := by
  constructor
  · have hv := Stage170SourceData.Window018.window.total_variance Stage170SourceData.Window018.valid hB hG hz hq
    norm_num [alpha, varianceIntercept, Stage170SourceData.Window018.window] at hv ⊢
    exact hv
  constructor
  · exact Stage170SourceData.Window018.window.available_variance Stage170SourceData.Window018.valid hB hG hz hS hq hrank
  intro i _
  fin_cases i
  · exact Stage170SourceData.Rate041.certificate.actual_laplace Stage170SourceData.Window018.window Stage170SourceData.Window018.valid Stage170SourceData.Rate041.checked hB hG hz hS hq hrank
  · exact Stage170SourceData.Rate223.certificate.actual_laplace Stage170SourceData.Window018.window Stage170SourceData.Window018.valid Stage170SourceData.Rate223.checked hB hG hz hS hq hrank
  · have hdensity : (BridgeFlowData.Stage130.Cell018Term02.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
      norm_num [BridgeFlowData.Stage130.Cell018Term02.rho]
      linarith
    exact BridgeFlowData.Stage130.Cell018Term02.actual_laplace hB hG hz hq hdensity

#print axioms actual_inputs
end ForestUnimodality.Stage130SourceData.Cell018
