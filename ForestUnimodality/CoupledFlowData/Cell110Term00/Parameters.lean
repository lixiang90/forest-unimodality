import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell110Term00
open CoupledFlow


def environment : Environment := ⟨(10429/10175), (5227/5075), (6542420847062628631818674070500377924761/2500000000000000000000000000000000000000), (9042420847062628631818674070500377924761/2500000000000000000000000000000000000000), 7, (541482288337639088285434450833802052883/400000000000000000000000000000000000000), (1835167298295335269210491530440903724043/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (10429/20604)

def qb : ℚ := (5227/10302)

def rho : ℚ := (280553856589125894230675227333/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (138740854997490730566660132527/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell110Term00
