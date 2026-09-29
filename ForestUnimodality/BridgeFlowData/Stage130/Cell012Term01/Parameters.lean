import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell012Term01
open CoupledFlow


def environment : Environment := ⟨(29/56), (89/166), (17921568627450980392156862745098039215687/10000000000000000000000000000000000000000), (27921568627450980392156862745098039215687/10000000000000000000000000000000000000000), 1, (1485340407297839211527588711882138180527/2000000000000000000000000000000000000000), (1218146866589773164167627835447904652057/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (29/85)

def qb : ℚ := (89/255)

def rho : ℚ := (1/4)

def retention : ℚ := (1/20)

def rate : ℚ := (48834245672578512252003475891/250000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell012Term01
