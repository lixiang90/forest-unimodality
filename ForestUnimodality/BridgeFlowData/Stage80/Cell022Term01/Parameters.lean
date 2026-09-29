import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell022Term01
open CoupledFlow


def environment : Environment := ⟨(64/89), (65/88), (11993464052287581699346405228758169934641/5000000000000000000000000000000000000000), (16993464052287581699346405228758169934641/5000000000000000000000000000000000000000), 2, (10821375894820176368235992406652248452141/10000000000000000000000000000000000000000), (7219445512409756931094878038361314024521/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (64/153)

def qb : ℚ := (65/153)

def rho : ℚ := (1/4)

def retention : ℚ := (1/10)

def rate : ℚ := (8908903897281259140575550547/40000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell022Term01
