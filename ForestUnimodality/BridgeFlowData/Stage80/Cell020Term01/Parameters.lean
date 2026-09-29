import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell020Term01
open CoupledFlow


def environment : Environment := ⟨(103/152), (7/10), (4588235294117647058823529411764705882353/2000000000000000000000000000000000000000), (6588235294117647058823529411764705882353/2000000000000000000000000000000000000000), 1, (4563367905790482713811582805112788463509/5000000000000000000000000000000000000000), (6782006920415224913494809688581314878893/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (103/255)

def qb : ℚ := (7/17)

def rho : ℚ := (1/4)

def retention : ℚ := (1/20)

def rate : ℚ := (11266820391827821646509430441/50000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell020Term01
