import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell030Term00
open CoupledFlow


def environment : Environment := ⟨(22/25), (1677/1895), (86121220604703247480403135498320268757/31250000000000000000000000000000000000), (117371220604703247480403135498320268757/31250000000000000000000000000000000000), 3, (12708168738152240142846533955958661493431/10000000000000000000000000000000000000000), (8816642192792266339289409103278077971131/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (22/47)

def qb : ℚ := (1677/3572)

def rho : ℚ := (1/4)

def retention : ℚ := (7/10)

def rate : ℚ := (30370523348440347395636625827/250000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell030Term00
