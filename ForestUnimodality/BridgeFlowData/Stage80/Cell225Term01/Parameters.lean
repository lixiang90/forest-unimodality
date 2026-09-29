import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell225Term01
open CoupledFlow


def environment : Environment := ⟨(467/275), (236/135), (30410923578582324828743502800542742557747/10000000000000000000000000000000000000000), (40410923578582324828743502800542742557747/10000000000000000000000000000000000000000), 15, (6443319992150670422297687075519225931389/2000000000000000000000000000000000000000), (25706140066160185066262713371773820063689/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (467/742)

def qb : ℚ := (236/371)

def rho : ℚ := (31482507305024346618170992963/100000000000000000000000000000)

def retention : ℚ := (1/5)

def rate : ℚ := (10649944716578451475063453731/50000000000000000000000000000)

def finish : ℚ := (3218875824868200749201518666452375279/2000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell225Term01
