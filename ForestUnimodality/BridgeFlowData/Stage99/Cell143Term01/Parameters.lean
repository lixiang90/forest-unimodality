import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell143Term01
open CoupledFlow


def environment : Environment := ⟨(47837/42475), (95699/84925), (13545269857755168830543537481813876269733/5000000000000000000000000000000000000000), (18545269857755168830543537481813876269733/5000000000000000000000000000000000000000), 10, (15056846218228715928718808234234785040953/10000000000000000000000000000000000000000), (2456434056544689385012769611834676102203/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (47837/90312)

def qb : ℚ := (95699/180624)

def rho : ℚ := (285692465321252247363576518949/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (72720137192083386643803916729/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell143Term01
