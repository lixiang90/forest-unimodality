import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell108Term00
open CoupledFlow


def environment : Environment := ⟨(109/100), (4583/4195), (5366897331837040800951858018026556078457/2000000000000000000000000000000000000000), (7366897331837040800951858018026556078457/2000000000000000000000000000000000000000), 9, (14493553637972955251501492275468193801133/10000000000000000000000000000000000000000), (1923131150137227044358758560982895107517/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (109/209)

def qb : ℚ := (4583/8778)

def rho : ℚ := (283484719709560213395228539141/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (142557522198835744468377861987/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell108Term00
