import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell014Term01
open CoupledFlow


def environment : Environment := ⟨(91/164), (31/54), (9588235294117647058823529411764705882353/5000000000000000000000000000000000000000), (14588235294117647058823529411764705882353/5000000000000000000000000000000000000000), 1, (1570611584052046111945590436118041384769/2000000000000000000000000000000000000000), (10640830449826989619377162629757785467129/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (91/255)

def qb : ℚ := (31/85)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (127709926211458659567205181/625000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell014Term01
