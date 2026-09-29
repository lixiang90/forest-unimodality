import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell084Term02
open CoupledFlow


def environment : Environment := ⟨(53/50), (21967/20675), (26589317498644688245988626879913891525651/10000000000000000000000000000000000000000), (36589317498644688245988626879913891525651/10000000000000000000000000000000000000000), 9, (14379099027442358435864994614485230927297/10000000000000000000000000000000000000000), (18848964342496315057915486296868544044463/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (53/103)

def qb : ℚ := (21967/42642)

def rho : ℚ := (35198072720013549150558574383/125000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (268274007239063839893535062531/1000000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell084Term02
