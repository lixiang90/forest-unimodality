import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell102Term00
open CoupledFlow


def environment : Environment := ⟨(203/201), (407/401), (5215989258320740406761419149174184277401/2000000000000000000000000000000000000000), (7215989258320740406761419149174184277401/2000000000000000000000000000000000000000), 7, (2699410666825370085340034493691349055961/2000000000000000000000000000000000000000), (18173933342429092484850851446249337876871/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (203/404)

def qb : ℚ := (407/808)

def rho : ℚ := (279220410815494811999635067933/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (13742747909404248752725814831/100000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell102Term00
