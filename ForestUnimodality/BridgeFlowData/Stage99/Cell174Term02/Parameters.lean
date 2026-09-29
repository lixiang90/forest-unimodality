import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell174Term02
open CoupledFlow


def environment : Environment := ⟨(3/2), (123/80), (3731772698339551468304856967713043716687/1250000000000000000000000000000000000000), (4981772698339551468304856967713043716687/1250000000000000000000000000000000000000), 15, (6339938421665658800078433658977658192747/2000000000000000000000000000000000000000), (12074050086616055775398963685294667530099/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (3/5)

def qb : ℚ := (123/203)

def rho : ℚ := (304064118707791611770873481409/1000000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (47509653998132714116558759727/250000000000000000000000000000)

def finish : ℚ := (1897119984885881302039978339220015071/1000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell174Term02
