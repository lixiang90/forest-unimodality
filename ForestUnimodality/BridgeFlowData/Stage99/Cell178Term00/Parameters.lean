import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell178Term00
open CoupledFlow


def environment : Environment := ⟨(33/20), (467/275), (15319096429494955000787154075332809807427/5000000000000000000000000000000000000000), (20319096429494955000787154075332809807427/5000000000000000000000000000000000000000), 15, (32427560458631188161704826856236440711141/10000000000000000000000000000000000000000), (25576868012329229071071700682427013962449/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (33/53)

def qb : ℚ := (467/742)

def rho : ℚ := (154874026040536750782129786601/500000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (29650275219150390077436525179/500000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell178Term00
