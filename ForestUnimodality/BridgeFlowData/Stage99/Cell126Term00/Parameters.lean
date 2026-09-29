import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell126Term00
open CoupledFlow


def environment : Environment := ⟨(23557/21175), (11791/10575), (6753199837017778506431744002780138379021/2500000000000000000000000000000000000000), (9253199837017778506431744002780138379021/2500000000000000000000000000000000000000), 10, (15019461859493549816804886802332501163299/10000000000000000000000000000000000000000), (3902512001369100469260008710964163878281/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (23557/44732)

def qb : ℚ := (11791/22366)

def rho : ℚ := (284865845349333372561214903779/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (72037924865658710801792343871/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell126Term00
