import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell004Term01
open CoupledFlow


def environment : Environment := ⟨(39/101), (2/5), (6428571428571428571428571428571428571429/5000000000000000000000000000000000000000), (11428571428571428571428571428571428571429/5000000000000000000000000000000000000000), 0, (1152857142857142857142857142857142857143/2500000000000000000000000000000000000000), (6530612244897959183673469387755102040817/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (39/140)

def qb : ℚ := (2/7)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (44957735004316453062289087759/250000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell004Term01
