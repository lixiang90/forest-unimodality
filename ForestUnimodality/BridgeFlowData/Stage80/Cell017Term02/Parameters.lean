import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell017Term02
open CoupledFlow


def environment : Environment := ⟨(97/158), (33/52), (5264705882352941176470588235294117647059/2500000000000000000000000000000000000000), (7764705882352941176470588235294117647059/2500000000000000000000000000000000000000), 1, (4245390475640307864844492054071740352881/5000000000000000000000000000000000000000), (12058131487889273356401384083044982698963/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (97/255)

def qb : ℚ := (33/85)

def rho : ℚ := (1/4)

def retention : ℚ := (1/20)

def rate : ℚ := (214709976602978946878089683521/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell017Term02
