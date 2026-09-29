import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell030Term01
open CoupledFlow


def environment : Environment := ⟨(1613/1865), (22/25), (25329513705136062637728406510598833920971/10000000000000000000000000000000000000000), (35329513705136062637728406510598833920971/10000000000000000000000000000000000000000), 3, (2954060326832855644658930744772841368457/2500000000000000000000000000000000000000), (1653721918112751868148989240921647545237/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (1613/3478)

def qb : ℚ := (22/47)

def rho : ℚ := (132491239559555667722491054517/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (64293836046108424769647804951/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell030Term01
