import ForestUnimodality.BridgeFlowData.Stage130.Cell018Term02.Complete
import ForestUnimodality.CoupledFlowNormalized

namespace ForestUnimodality.BridgeFlowData.Stage80.Cell018Term01
open CoupledFlow
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qa : ℚ := (33/85)
def qb : ℚ := (101/255)
def rho : ℚ := (1/4)
def retention : ℚ := (1/100)
def rate : ℚ := (219492563790003320359013525047/1000000000000000000000000000000)
def table : Table := { BridgeFlowData.Stage130.Cell018Term02.table with rate := rate }

theorem header_checked : table.headerCheck=true := by
  have h : BridgeFlowData.Stage130.Cell018Term02.table.HeaderAccepts := of_decide_eq_true BridgeFlowData.Stage130.Cell018Term02.header_checked
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
  have hdensitySource : (BridgeFlowData.Stage130.Cell018Term02.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
    have hr : (BridgeFlowData.Stage130.Cell018Term02.rho:ℝ)≤(rho:ℝ) := by norm_num [BridgeFlowData.Stage130.Cell018Term02.rho,rho]
    exact (mul_le_mul_of_nonneg_right hr (by positivity)).trans hdensity
  exact table.actual_laplace_normalized BridgeFlowData.Stage130.Cell018Term02.normalization_checked (le_refl _) header_checked
    BridgeFlowData.Stage130.Cell018Term02.table_rows_checked BridgeFlowData.Stage130.Cell018Term02.connections_checked hB hG hz hq hdensitySource

#print axioms header_checked
#print axioms actual_laplace
end ForestUnimodality.BridgeFlowData.Stage80.Cell018Term01
