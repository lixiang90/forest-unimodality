import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell031Term00
open CoupledFlow


def environment : Environment := ⟨(1677/1895), (841/945), (27670772676371780515117581187010078387459/10000000000000000000000000000000000000000), (37670772676371780515117581187010078387459/10000000000000000000000000000000000000000), 3, (12752930796447649572884320284931116925549/10000000000000000000000000000000000000000), (8869294462717991996980371158531768175771/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (1677/3572)

def qb : ℚ := (841/1786)

def rho : ℚ := (1/4)

def retention : ℚ := (7/10)

def rate : ℚ := (121833317890533532331598491391/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell031Term00
