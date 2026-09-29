import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell153Term02
open CoupledFlow


def environment : Environment := ⟨(32351/28425), (48539/42625), (27181773510386767506352909009590686630709/10000000000000000000000000000000000000000), (37181773510386767506352909009590686630709/10000000000000000000000000000000000000000), 10, (604028660913414896686815722101518749531/400000000000000000000000000000000000000), (9898458297248164341137202461588578486947/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (32351/60776)

def qb : ℚ := (48539/91164)

def rho : ℚ := (286396263034078545196695374587/1000000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (276575499377136723072653860679/1000000000000000000000000000000)

def finish : ℚ := (18971199848858813/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell153Term02
