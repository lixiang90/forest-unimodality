import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell030Term00
open CoupledFlow


def environment : Environment := ⟨(22/25), (1677/1895), (5053314365588382775219659667330651086703/2000000000000000000000000000000000000000), (7053314365588382775219659667330651086703/2000000000000000000000000000000000000000), 3, (11791033643745838740764592317563234389787/10000000000000000000000000000000000000000), (258705036374311439539372403024248973623/156250000000000000000000000000000000000)⟩

def qa : ℚ := (22/47)

def qb : ℚ := (1677/3572)

def rho : ℚ := (266249231543870864733613170907/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (129338063533614766350041288437/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell030Term00
