import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell121Term00
open CoupledFlow


def environment : Environment := ⟨(2326/2105), (4657/4205), (5390791567362222630470396572161226424831/2000000000000000000000000000000000000000), (7390791567362222630470396572161226424831/2000000000000000000000000000000000000000), 10, (46847388165679621676659658552943006143/31250000000000000000000000000000000000), (19419384071996090493173457930802771079011/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2326/4431)

def qb : ℚ := (4657/8862)

def rho : ℚ := (71102281696885723082724336389/250000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (49903308909452323233113304277/500000000000000000000000000000)

def finish : ℚ := (2231435513142097/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell121Term00
