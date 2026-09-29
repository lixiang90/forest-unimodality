import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell133Term00
open CoupledFlow


def environment : Environment := ⟨(107/100), (7427/6925), (41233500359868820658216603768442627961/15625000000000000000000000000000000000), (56858500359868820658216603768442627961/15625000000000000000000000000000000000), 9, (892860724120464117056884326950092220611/625000000000000000000000000000000000000), (4707782409952572252269506312020327735411/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (107/207)

def qb : ℚ := (7427/14352)

def rho : ℚ := (284417044314334994308742645149/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (14071749997318988471681179241/100000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell133Term00
