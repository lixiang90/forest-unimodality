import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell070Term00
open CoupledFlow


def environment : Environment := ⟨(10429/10175), (5227/5075), (26335056373277005930606404104911478860931/10000000000000000000000000000000000000000), (36335056373277005930606404104911478860931/10000000000000000000000000000000000000000), 7, (6805385417678860512160122651435950438851/5000000000000000000000000000000000000000), (737423178657033236262006112430100174747/400000000000000000000000000000000000000)⟩

def qa : ℚ := (10429/20604)

def qb : ℚ := (5227/10302)

def rho : ℚ := (69819240556101356567561720761/250000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (69369853939743167177454982777/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell070Term00
