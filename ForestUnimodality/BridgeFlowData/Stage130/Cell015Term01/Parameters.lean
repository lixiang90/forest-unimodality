import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell015Term01
open CoupledFlow


def environment : Environment := ⟨(31/54), (19/32), (1237745098039215686274509803921568627451/625000000000000000000000000000000000000), (1862745098039215686274509803921568627451/625000000000000000000000000000000000000), 1, (126028978004302326589807696807380323547/156250000000000000000000000000000000000), (1110342176086120722798923490965013456363/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (31/85)

def qb : ℚ := (19/51)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (104068049568406857188712842767/500000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell015Term01
