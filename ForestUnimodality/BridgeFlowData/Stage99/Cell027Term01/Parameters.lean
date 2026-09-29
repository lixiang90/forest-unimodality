import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell027Term01
open CoupledFlow


def environment : Environment := ⟨(301/365), (17/20), (26756756756756756756756756756756756756757/10000000000000000000000000000000000000000), (36756756756756756756756756756756756756757/10000000000000000000000000000000000000000), 2, (742855861885479570845566682982162161231/625000000000000000000000000000000000000), (3377647918188458728999269539810080350621/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (301/666)

def qb : ℚ := (17/37)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (63775958493199744064885187991/250000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell027Term01
