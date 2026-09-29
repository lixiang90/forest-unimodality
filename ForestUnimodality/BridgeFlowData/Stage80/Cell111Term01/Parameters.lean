import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell111Term01
open CoupledFlow


def environment : Environment := ⟨(27/25), (22597/20875), (26496115143188163415570122417946210604383/10000000000000000000000000000000000000000), (36496115143188163415570122417946210604383/10000000000000000000000000000000000000000), 9, (14335582541255754819382489856449846999123/10000000000000000000000000000000000000000), (18970894228253195820335803650127220303351/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (27/52)

def qb : ℚ := (22597/43472)

def rho : ℚ := (35606930354319751776102849643/125000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (269790450415958260378967757429/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell111Term01
