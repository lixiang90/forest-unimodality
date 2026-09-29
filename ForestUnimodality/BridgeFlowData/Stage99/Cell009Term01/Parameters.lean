import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell009Term01
open CoupledFlow


def environment : Environment := ⟨(20/43), (41/85), (1001984126984126984126984126984126984127/625000000000000000000000000000000000000), (1626984126984126984126984126984126984127/625000000000000000000000000000000000000), 0, (343458571120616629536984710364190830897/625000000000000000000000000000000000000), (8470647518266565885613504661123708742757/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (20/63)

def qb : ℚ := (41/126)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (98494759447971526062487597933/500000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell009Term01
