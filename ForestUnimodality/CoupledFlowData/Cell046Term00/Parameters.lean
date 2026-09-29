import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell046Term00
open CoupledFlow


def environment : Environment := ⟨(581/635), (23/25), (25468027425764256372072421781581547949477/10000000000000000000000000000000000000000), (35468027425764256372072421781581547949477/10000000000000000000000000000000000000000), 4, (6221376976952811134974637065513429146639/5000000000000000000000000000000000000000), (8497548237422686422475684385170579196229/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (581/1216)

def qb : ℚ := (23/48)

def rho : ℚ := (135098200109825166189862266671/500000000000000000000000000000)

def retention : ℚ := (1/2)

def rate : ℚ := (194340200073128356336240233209/1000000000000000000000000000000)

def finish : ℚ := (13862943611198906188344642429163531361/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell046Term00
