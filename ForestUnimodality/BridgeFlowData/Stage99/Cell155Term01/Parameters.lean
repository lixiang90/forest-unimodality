import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell155Term01
open CoupledFlow


def environment : Environment := ⟨(97103/85225), (57/50), (5438269008711990116371410288068251728141/2000000000000000000000000000000000000000), (7438269008711990116371410288068251728141/2000000000000000000000000000000000000000), 10, (3021063774370647817446348227766988850959/2000000000000000000000000000000000000000), (154782905044021406481151572145111838677/78125000000000000000000000000000000000)⟩

def qa : ℚ := (97103/182328)

def qb : ℚ := (57/107)

def rho : ℚ := (71617506673918456753660491497/250000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (92578316295246968490543915087/500000000000000000000000000000)

def finish : ℚ := (1021651245531981/2000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell155Term01
