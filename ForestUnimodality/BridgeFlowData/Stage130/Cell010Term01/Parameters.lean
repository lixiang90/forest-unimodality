import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell010Term01
open CoupledFlow


def environment : Environment := ⟨(41/85), (1/2), (16666666666666666666666666666666666666667/10000000000000000000000000000000000000000), (26666666666666666666666666666666666666667/10000000000000000000000000000000000000000), 0, (2835508968617646801025674544841337618569/5000000000000000000000000000000000000000), (8888888888888888888888888888888888888889/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (41/126)

def qb : ℚ := (1/3)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (100372837919489952261725275127/500000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell010Term01
