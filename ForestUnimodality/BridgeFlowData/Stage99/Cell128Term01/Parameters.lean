import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell128Term01
open CoupledFlow


def environment : Environment := ⟨(11791/10575), (23607/21125), (27032392541893770518771351485932550574337/10000000000000000000000000000000000000000), (37032392541893770518771351485932550574337/10000000000000000000000000000000000000000), 10, (15028884191716208516408654711003416012959/10000000000000000000000000000000000000000), (19543586039892833779769187483868588961111/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (11791/22366)

def qb : ℚ := (23607/44732)

def rho : ℚ := (285016963014227600337278835259/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (4513728084404919206744352539/31250000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell128Term01
