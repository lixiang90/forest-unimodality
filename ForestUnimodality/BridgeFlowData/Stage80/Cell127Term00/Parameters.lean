import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell127Term00
open CoupledFlow


def environment : Environment := ⟨(11/10), (1549/1405), (1330366969410476645136839687407782849359/500000000000000000000000000000000000000), (1830366969410476645136839687407782849359/500000000000000000000000000000000000000), 10, (14824444109639653256607739157927209445523/10000000000000000000000000000000000000000), (4798981779987861075350312585976058960151/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (11/21)

def qb : ℚ := (1549/2954)

def rho : ℚ := (143242786637413455921120879643/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (2859297825315212887667761929/20000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell127Term00
