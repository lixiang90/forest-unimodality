import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell027Term00
open CoupledFlow


def environment : Environment := ⟨(301/365), (17/20), (3158812829410854931752838317935892889751/1250000000000000000000000000000000000000), (4408812829410854931752838317935892889751/1250000000000000000000000000000000000000), 2, (226298653636987442927127260847577216261/200000000000000000000000000000000000000), (202567075945904145512968247040297781421/125000000000000000000000000000000000000)⟩

def qa : ℚ := (301/666)

def qb : ℚ := (17/37)

def rho : ℚ := (52106936406376832816242535427/200000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (62177178753663060295449718639/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell027Term00
