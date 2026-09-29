import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell214Term01
open CoupledFlow


def environment : Environment := ⟨(107/80), (27/20), (28274717256248485273701171610525376679409/10000000000000000000000000000000000000000), (38274717256248485273701171610525376679409/10000000000000000000000000000000000000000), 14, (9934867375104165684715881566549526407931/5000000000000000000000000000000000000000), (21987603530185300050849609223067769581789/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (107/187)

def qb : ℚ := (27/47)

def rho : ℚ := (150090745611608403810248361647/500000000000000000000000000000)

def retention : ℚ := (3/10)

def rate : ℚ := (11936671045313439183023595431/62500000000000000000000000000)

def finish : ℚ := (120397280432593599262274621776183850293/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell214Term01
