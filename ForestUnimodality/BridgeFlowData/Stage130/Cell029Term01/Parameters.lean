import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell029Term01
open CoupledFlow


def environment : Environment := ⟨(1613/1865), (22/25), (13723404255319148936170212765957446808511/5000000000000000000000000000000000000000), (18723404255319148936170212765957446808511/5000000000000000000000000000000000000000), 3, (12663402961235333431969021641328199459159/10000000000000000000000000000000000000000), (8764146672702580353100950656405613399729/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (1613/3478)

def qb : ℚ := (22/47)

def rho : ℚ := (1/4)

def retention : ℚ := (3/5)

def rate : ℚ := (150897756728746503562907367693/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell029Term01
