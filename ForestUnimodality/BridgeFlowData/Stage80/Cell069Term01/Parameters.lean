import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell069Term01
open CoupledFlow


def environment : Environment := ⟨(9529/9875), (4777/4925), (3230801918803280714838981074720534878853/1250000000000000000000000000000000000000), (4480801918803280714838981074720534878853/1250000000000000000000000000000000000000), 5, (649861644535924726785383377219009621123/500000000000000000000000000000000000000), (17649796550091339496834312590344254888709/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (9529/19404)

def qb : ℚ := (4777/9702)

def rho : ℚ := (137356190805998177808947192019/500000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (270625209721069732031127368413/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell069Term01
