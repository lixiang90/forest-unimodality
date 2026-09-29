import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell078Term01
open CoupledFlow


def environment : Environment := ⟨(49/50), (131/133), (5188393718687498508807443750280407193401/2000000000000000000000000000000000000000), (7188393718687498508807443750280407193401/2000000000000000000000000000000000000000), 5, (6519289606677007331089440058232402508871/5000000000000000000000000000000000000000), (1783484047628905880026089263800631330181/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (49/99)

def qb : ℚ := (131/264)

def rho : ℚ := (55223699828475471717903324081/200000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (17141823529234030000483556033/62500000000000000000000000000)

def finish : ℚ := (11437166434867217/5000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell078Term01
