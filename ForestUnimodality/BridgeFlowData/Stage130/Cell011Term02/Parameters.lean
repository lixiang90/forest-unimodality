import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell011Term02
open CoupledFlow


def environment : Environment := ⟨(1/2), (29/56), (17294117647058823529411764705882352941177/10000000000000000000000000000000000000000), (27294117647058823529411764705882352941177/10000000000000000000000000000000000000000), 1, (7213097752241473918413444981375698245291/10000000000000000000000000000000000000000), (2328027681660899653979238754325259515571/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (1/3)

def qb : ℚ := (29/85)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (96365417595185975936879833599/500000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell011Term02
