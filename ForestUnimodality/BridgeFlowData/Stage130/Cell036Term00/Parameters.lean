import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell036Term00
open CoupledFlow


def environment : Environment := ⟨(869/955), (581/635), (14111842105263157894736842105263157894737/5000000000000000000000000000000000000000), (19111842105263157894736842105263157894737/5000000000000000000000000000000000000000), 4, (13597950799487798511724995448894934446419/10000000000000000000000000000000000000000), (228289067910318559556786703601108033241/125000000000000000000000000000000000000)⟩

def qa : ℚ := (869/1824)

def qb : ℚ := (581/1216)

def rho : ℚ := (1/4)

def retention : ℚ := (3/5)

def rate : ℚ := (7664271205993162166618808381/50000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell036Term00
