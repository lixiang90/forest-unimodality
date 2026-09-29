import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell242Term00
open CoupledFlow


def environment : Environment := ⟨(107/49), (9/4), (8192949953374923848375926728931008111633/2500000000000000000000000000000000000000), (10692949953374923848375926728931008111633/2500000000000000000000000000000000000000), 15, (34406810917064523419196493337574397209923/10000000000000000000000000000000000000000), (7402811506182639587337180043106082538823/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (107/156)

def qb : ℚ := (9/13)

def rho : ℚ := (20232597626426781312094726519/62500000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (6194046934040984496806347819/50000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell242Term00
