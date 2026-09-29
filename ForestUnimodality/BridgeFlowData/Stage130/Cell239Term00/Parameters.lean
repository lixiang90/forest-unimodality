import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell239Term00
open CoupledFlow


def environment : Environment := ⟨2, (35/17), (1005599848055304987822276220972800027979/312500000000000000000000000000000000000), (1318099848055304987822276220972800027979/312500000000000000000000000000000000000), 15, (1354291758370029685575184935093840643341/400000000000000000000000000000000000000), (7097460720297796088273795036007384766041/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (2/3)

def qb : ℚ := (35/52)

def rho : ℚ := (159575572952128233929977158889/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (119984313105215384271646889291/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell239Term00
