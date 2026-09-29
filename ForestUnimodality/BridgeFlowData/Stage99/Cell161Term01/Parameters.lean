import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell161Term01
open CoupledFlow


def environment : Environment := ⟨(49/40), (99/80), (6994226373270947709806638816353045869829/2500000000000000000000000000000000000000), (9494226373270947709806638816353045869829/2500000000000000000000000000000000000000), 13, (17308289310853277965624798484904800393011/10000000000000000000000000000000000000000), (21003986836956956944600161850702827734371/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (49/89)

def qb : ℚ := (99/179)

def rho : ℚ := (291267873733971030985799191897/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (227893728886710581129165379167/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell161Term01
