import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell029Term01
open CoupledFlow


def environment : Environment := ⟨(1613/1865), (22/25), (27342053507638646190416897853778881502899/10000000000000000000000000000000000000000), (37342053507638646190416897853778881502899/10000000000000000000000000000000000000000), 3, (12621522868688121590803231242884291650949/10000000000000000000000000000000000000000), (17479259088681919493386633037939050916251/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (1613/3478)

def qb : ℚ := (22/47)

def rho : ℚ := (250701320583362020534797923337/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (25713930337751373739741906867/200000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell029Term01
