import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell186Term01
open CoupledFlow


def environment : Environment := ⟨(427/365), (2567/2185), (6769477810435318363009246875929256916209/2500000000000000000000000000000000000000), (9269477810435318363009246875929256916209/2500000000000000000000000000000000000000), 12, (3921122569413584573574982619686049820579/2500000000000000000000000000000000000000), (625914076688432824017380490596338449703/312500000000000000000000000000000000000)⟩

def qa : ℚ := (427/792)

def qb : ℚ := (2567/4752)

def rho : ℚ := (291382974176532292565698943147/1000000000000000000000000000000)

def retention : ℚ := (1/5)

def rate : ℚ := (55773305484042383210159394197/250000000000000000000000000000)

def finish : ℚ := (16094379124341003/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell186Term01
