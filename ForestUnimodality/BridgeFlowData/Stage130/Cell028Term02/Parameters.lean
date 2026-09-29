import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell028Term02
open CoupledFlow


def environment : Environment := ⟨(17/20), (1613/1865), (2710178263369752731454859114433582518689/1000000000000000000000000000000000000000), (3710178263369752731454859114433582518689/1000000000000000000000000000000000000000), 3, (2505090433816297474991654853142658031571/2000000000000000000000000000000000000000), (8603389216238371414371316491635089998053/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (17/37)

def qb : ℚ := (1613/3478)

def rho : ℚ := (1/4)

def retention : ℚ := (1/20)

def rate : ℚ := (237892838390995600671913371087/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell028Term02
