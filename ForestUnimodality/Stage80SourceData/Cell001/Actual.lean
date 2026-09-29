import ForestUnimodality.Stage80KernelData.Cell001.Budget
import ForestUnimodality.BridgeFlowData.Stage99.Cell001Term02.Actual
import ForestUnimodality.Stage170SourceData.Windows.Batch000_019

namespace ForestUnimodality.Stage80SourceData.Cell001
open Stage80KernelData.Cell001
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
  · have hv := Stage170SourceData.Window001.window.total_variance Stage170SourceData.Window001.valid hB hG hz hq
    norm_num [alpha, varianceIntercept, Stage170SourceData.Window001.window] at hv ⊢
    exact hv
  constructor
  · exact Stage170SourceData.Window001.window.available_variance Stage170SourceData.Window001.valid hB hG hz hS hq hrank
  intro i _
  fin_cases i
  · have hdensity : (BridgeFlowData.Stage99.Cell001Term02.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
      norm_num [BridgeFlowData.Stage99.Cell001Term02.rho]
      linarith
    exact BridgeFlowData.Stage99.Cell001Term02.actual_laplace hB hG hz hq hdensity

#print axioms actual_inputs
end ForestUnimodality.Stage80SourceData.Cell001
