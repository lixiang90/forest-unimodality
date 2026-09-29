import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell132Term01
open CoupledFlow


def environment : Environment := ⟨(94503/84425), (28/25), (27037269758479391261627825367329028063167/10000000000000000000000000000000000000000), (37037269758479391261627825367329028063167/10000000000000000000000000000000000000000), 10, (15031229614154693989503654994072037120963/10000000000000000000000000000000000000000), (76433044902522328664915913199087027253/39062500000000000000000000000000000000)⟩

def qa : ℚ := (94503/178928)

def qb : ℚ := (28/53)

def rho : ℚ := (285281226309346019391714104291/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (144777482957365241659419214167/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell132Term01
