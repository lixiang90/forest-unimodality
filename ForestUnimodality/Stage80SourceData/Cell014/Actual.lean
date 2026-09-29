import ForestUnimodality.Stage80KernelData.Cell014.Budget
import ForestUnimodality.BridgeAffineRateData.Stage80.Cell014Term00
import ForestUnimodality.BridgeFlowData.Stage80.Cell014Term01.Actual
import ForestUnimodality.Stage170SourceData.Windows.Batch000_019

namespace ForestUnimodality.Stage80SourceData.Cell014
open Stage80KernelData.Cell014
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
  · have hv := Stage170SourceData.Window014.window.total_variance Stage170SourceData.Window014.valid hB hG hz hq
    norm_num [alpha, varianceIntercept, Stage170SourceData.Window014.window] at hv ⊢
    exact hv
  constructor
  · exact Stage170SourceData.Window014.window.available_variance Stage170SourceData.Window014.valid hB hG hz hS hq hrank
  intro i _
  fin_cases i
  · exact BridgeAffineRateData.Stage80.Cell014Term00.certificate.actual_laplace Stage170SourceData.Window014.window Stage170SourceData.Window014.valid BridgeAffineRateData.Stage80.Cell014Term00.checked hB hG hz hS hq hrank
  · have hdensity : (BridgeFlowData.Stage80.Cell014Term01.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
      norm_num [BridgeFlowData.Stage80.Cell014Term01.rho]
      linarith
    exact BridgeFlowData.Stage80.Cell014Term01.actual_laplace hB hG hz hq hdensity

#print axioms actual_inputs
end ForestUnimodality.Stage80SourceData.Cell014
