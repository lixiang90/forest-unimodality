import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell145Term01
open CoupledFlow


def environment : Environment := ⟨(7977/7075), (95749/84875), (5420045058793886923139616330593513996581/2000000000000000000000000000000000000000), (7420045058793886923139616330593513996581/2000000000000000000000000000000000000000), 10, (301230074642464037480560177485051846271/200000000000000000000000000000000000000), (19666874123440292513832467557965673765907/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (7977/15052)

def qb : ℚ := (95749/180624)

def rho : ℚ := (285767108157544748566235626541/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (36379025912366983987263516273/250000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell145Term01
