import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell159Term02
open CoupledFlow


def environment : Environment := ⟨(6/5), (97/80), (5561180886909935854672802957793050063999/2000000000000000000000000000000000000000), (7561180886909935854672802957793050063999/2000000000000000000000000000000000000000), 13, (17216420048300935796830229227055999482667/10000000000000000000000000000000000000000), (20718490000854908980318132398472481813783/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (6/11)

def qb : ℚ := (97/177)

def rho : ℚ := (144956880959905067794634890843/500000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (222978849276824018772114160007/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell159Term02
