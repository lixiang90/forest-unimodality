import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell197Term00
open CoupledFlow


def environment : Environment := ⟨(97/80), (49/40), (13741054096626435271371967772709170927921/5000000000000000000000000000000000000000), (18741054096626435271371967772709170927921/5000000000000000000000000000000000000000), 13, (17042431166018943162212438879769220468471/10000000000000000000000000000000000000000), (20636216870442591647128683614893244392543/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (97/177)

def qb : ℚ := (49/89)

def rho : ℚ := (293773122319685984542196620841/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (17842022208000315737248440747/125000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell197Term00
