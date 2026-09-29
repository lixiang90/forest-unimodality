import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell015Term02
open CoupledFlow


def environment : Environment := ⟨(31/54), (19/32), (1237745098039215686274509803921568627451/625000000000000000000000000000000000000), (1862745098039215686274509803921568627451/625000000000000000000000000000000000000), 1, (126028978004302326589807696807380323547/156250000000000000000000000000000000000), (1110342176086120722798923490965013456363/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (31/85)

def qb : ℚ := (19/51)

def rho : ℚ := (1/4)

def retention : ℚ := (1/20)

def rate : ℚ := (41407252095423810665152055579/200000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell015Term02
