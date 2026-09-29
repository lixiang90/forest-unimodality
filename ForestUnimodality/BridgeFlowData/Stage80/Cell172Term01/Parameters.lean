import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell172Term01
open CoupledFlow


def environment : Environment := ⟨(97103/85225), (57/50), (26790472315392302264412484183972755987669/10000000000000000000000000000000000000000), (36790472315392302264412484183972755987669/10000000000000000000000000000000000000000), 10, (1491253501552671357564639446828373255027/1000000000000000000000000000000000000000), (4899665705554582310914746725435624045087/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (97103/182328)

def qb : ℚ := (57/107)

def rho : ℚ := (144795716621163852799578684659/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (146565787621483975393912770699/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell172Term01
