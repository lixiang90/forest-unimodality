import ForestUnimodality.BridgeFlowData.Stage99.Cell149Term01.Complete
import ForestUnimodality.CoupledFlowNormalized

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell166Term01
open CoupledFlow
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qa : ℚ := (113/213)
def qb : ℚ := (8069/15194)
def rho : ℚ := (72216037597735552297503272163/250000000000000000000000000000)
def retention : ℚ := (7/10)
def rate : ℚ := (72855762517983036438922591273/500000000000000000000000000000)
def table : Table := { BridgeFlowData.Stage99.Cell149Term01.table with rate := rate }

theorem header_checked : table.headerCheck=true := by
  have h : BridgeFlowData.Stage99.Cell149Term01.table.HeaderAccepts := of_decide_eq_true BridgeFlowData.Stage99.Cell149Term01.header_checked
  apply decide_eq_true
  rcases h with ⟨he,ht,hl,hu,hr,hx,hf,_⟩
  refine ⟨he,ht,hl,hu,hr,hx,hf,?_⟩
  decide +kernel

variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hdensitySource : (BridgeFlowData.Stage99.Cell149Term01.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
    have hr : (BridgeFlowData.Stage99.Cell149Term01.rho:ℝ)≤(rho:ℝ) := by norm_num [BridgeFlowData.Stage99.Cell149Term01.rho,rho]
    exact (mul_le_mul_of_nonneg_right hr (by positivity)).trans hdensity
  exact table.actual_laplace_normalized BridgeFlowData.Stage99.Cell149Term01.normalization_checked (le_refl _) header_checked
    BridgeFlowData.Stage99.Cell149Term01.table_rows_checked BridgeFlowData.Stage99.Cell149Term01.connections_checked hB hG hz hq hdensitySource

#print axioms header_checked
#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell166Term01
