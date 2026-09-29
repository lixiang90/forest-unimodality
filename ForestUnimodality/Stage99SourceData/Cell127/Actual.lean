import ForestUnimodality.Stage99SourceData.Cell127.Profiles
import ForestUnimodality.BridgeFlowData.Stage99.Cell127Term00.Actual
import ForestUnimodality.BridgeFlowData.Stage99.Cell127Term01.Actual
import ForestUnimodality.BridgeFlowData.Stage99.Cell127Term02.Actual
import ForestUnimodality.BridgeFlowData.Stage99.Cell127Term03.Actual

namespace ForestUnimodality.Stage99SourceData.Cell127
open Stage99KernelData.Cell127
variable {V : Type*} [DecidableEq V]

theorem actual_inputs {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card) (h8 : 8≤S.card) (hN : S.card≤129)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(alpha:ℝ))*hardCoreAvailableMean G S B z+varianceIntercept) ∧
    (hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z) ∧
    (∀i∈row.terms,hardCoreLayerLaplace G S B z (row.retention i)≤
      Real.exp (-(rate i:ℝ)*hardCoreAvailableMean G S B z)) := by
  refine ⟨actual_variance hB hG hS hN hz hq,
    actual_available_variance hB hG hz hS hq hrank, ?_⟩
  have hd := actual_density G hG S h8 hN hz hq hrank
  intro i _
  fin_cases i
  · have hdensity : (BridgeFlowData.Stage99.Cell127Term00.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
      simpa only [density,BridgeFlowData.Stage99.Cell127Term00.rho] using hd
    exact BridgeFlowData.Stage99.Cell127Term00.actual_laplace hB hG hz hq hdensity
  · have hdensity : (BridgeFlowData.Stage99.Cell127Term01.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
      simpa only [density,BridgeFlowData.Stage99.Cell127Term01.rho] using hd
    exact BridgeFlowData.Stage99.Cell127Term01.actual_laplace hB hG hz hq hdensity
  · have hdensity : (BridgeFlowData.Stage99.Cell127Term02.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
      simpa only [density,BridgeFlowData.Stage99.Cell127Term02.rho] using hd
    exact BridgeFlowData.Stage99.Cell127Term02.actual_laplace hB hG hz hq hdensity
  · have hdensity : (BridgeFlowData.Stage99.Cell127Term03.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
      simpa only [density,BridgeFlowData.Stage99.Cell127Term03.rho] using hd
    exact BridgeFlowData.Stage99.Cell127Term03.actual_laplace hB hG hz hq hdensity

#print axioms actual_inputs
end ForestUnimodality.Stage99SourceData.Cell127
