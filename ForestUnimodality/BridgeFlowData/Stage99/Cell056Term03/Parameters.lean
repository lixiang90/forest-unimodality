import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell056Term03
open CoupledFlow


def environment : Environment := ⟨(49/50), (131/133), (6565108046637625560565250228918739535231/2500000000000000000000000000000000000000), (9065108046637625560565250228918739535231/2500000000000000000000000000000000000000), 5, (13176355320774675451020924416186344038603/10000000000000000000000000000000000000000), (17992865971356499218697693636187195138111/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (49/99)

def qb : ℚ := (131/264)

def rho : ℚ := (136846720044383027944244616249/500000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (139065568779127528564495339393/500000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell056Term03
