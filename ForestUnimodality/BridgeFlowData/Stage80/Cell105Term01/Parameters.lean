import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell105Term01
open CoupledFlow


def environment : Environment := ⟨(107/100), (7427/6925), (26439469950452339159484903230425742047387/10000000000000000000000000000000000000000), (36439469950452339159484903230425742047387/10000000000000000000000000000000000000000), 9, (1430913308986021837291818557138833950177/1000000000000000000000000000000000000000), (18857019462235892066436341714908861913737/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (107/207)

def qb : ℚ := (7427/14352)

def rho : ℚ := (284026552763596577044802744559/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (6692709398513143281354296067/25000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell105Term01
