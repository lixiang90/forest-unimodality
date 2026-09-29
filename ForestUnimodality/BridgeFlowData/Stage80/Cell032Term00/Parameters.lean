import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell032Term00
open CoupledFlow


def environment : Environment := ⟨(841/945), (1687/1885), (25338911848502102467417235390909300142569/10000000000000000000000000000000000000000), (35338911848502102467417235390909300142569/10000000000000000000000000000000000000000), 3, (11820005054774217655018460380811843709457/10000000000000000000000000000000000000000), (4172504499469698128676713053223963419689/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (841/1786)

def qb : ℚ := (1687/3572)

def rho : ℚ := (427661778848349068731140391/1600000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (32616265371507799069390328927/250000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell032Term00
