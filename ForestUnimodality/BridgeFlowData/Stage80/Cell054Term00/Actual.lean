import ForestUnimodality.BridgeFlowData.Stage99.Cell048Term00.Complete
import ForestUnimodality.CoupledFlowNormalized

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell054Term00
open CoupledFlow
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qa : ℚ := (9237/19012)
def qb : ℚ := (4631/9506)
def rho : ℚ := (136400698935543597779231127479/500000000000000000000000000000)
def retention : ℚ := (4/5)
def rate : ℚ := (11600055181003644102969791193/125000000000000000000000000000)
def table : Table := { BridgeFlowData.Stage99.Cell048Term00.table with rate := rate }

theorem header_checked : table.headerCheck=true := by
  have h : BridgeFlowData.Stage99.Cell048Term00.table.HeaderAccepts := of_decide_eq_true BridgeFlowData.Stage99.Cell048Term00.header_checked
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
  have hdensitySource : (BridgeFlowData.Stage99.Cell048Term00.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
    have hr : (BridgeFlowData.Stage99.Cell048Term00.rho:ℝ)≤(rho:ℝ) := by norm_num [BridgeFlowData.Stage99.Cell048Term00.rho,rho]
    exact (mul_le_mul_of_nonneg_right hr (by positivity)).trans hdensity
  exact table.actual_laplace_normalized BridgeFlowData.Stage99.Cell048Term00.normalization_checked (le_refl _) header_checked
    BridgeFlowData.Stage99.Cell048Term00.table_rows_checked BridgeFlowData.Stage99.Cell048Term00.connections_checked hB hG hz hq hdensitySource

#print axioms header_checked
#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell054Term00
