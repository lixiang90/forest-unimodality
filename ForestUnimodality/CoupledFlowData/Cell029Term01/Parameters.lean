import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell029Term01
open CoupledFlow


def environment : Environment := ⟨(17/20), (1613/1865), (25218916734035309408742321475405785615187/10000000000000000000000000000000000000000), (35218916734035309408742321475405785615187/10000000000000000000000000000000000000000), 3, (1471493402930068923599336691370652785341/1250000000000000000000000000000000000000), (16333557415755880988010743110934310580017/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (17/37)

def qb : ℚ := (1613/3478)

def rho : ℚ := (65841361110495609306200918759/250000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (1985644530743636650539838207/15625000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell029Term01
