import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell039Term02
open CoupledFlow


def environment : Environment := ⟨(869/955), (581/635), (26777563624582228905138997973276231165779/10000000000000000000000000000000000000000), (36777563624582228905138997973276231165779/10000000000000000000000000000000000000000), 4, (12992039993824050823392723631887141835083/10000000000000000000000000000000000000000), (17572174725232134041024471893481488739571/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (869/1824)

def qb : ℚ := (581/1216)

def rho : ℚ := (259830182069058373820143042887/1000000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (16496591803061268688780524903/62500000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell039Term02
