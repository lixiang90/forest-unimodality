import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell174Term00
open CoupledFlow


def environment : Environment := ⟨(3/2), (123/80), (3731772698339551468304856967713043716687/1250000000000000000000000000000000000000), (4981772698339551468304856967713043716687/1250000000000000000000000000000000000000), 15, (6339938421665658800078433658977658192747/2000000000000000000000000000000000000000), (12074050086616055775398963685294667530099/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (3/5)

def qb : ℚ := (123/203)

def rho : ℚ := (304064118707791611770873481409/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (26824956385945856860274604611/200000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell174Term00
