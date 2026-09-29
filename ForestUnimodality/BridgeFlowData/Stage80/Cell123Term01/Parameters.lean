import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell123Term01
open CoupledFlow


def environment : Environment := ⟨(2294/2095), (1531/1395), (26579911026793716168333707003451636200637/10000000000000000000000000000000000000000), (36579911026793716168333707003451636200637/10000000000000000000000000000000000000000), 9, (14374707264990954419716606697666368841253/10000000000000000000000000000000000000000), (19140069645256725718974335414314577929999/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2294/4389)

def qb : ℚ := (1531/2926)

def rho : ℚ := (286080476026036328096079439561/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (273043262606797890927138091157/1000000000000000000000000000000)

def finish : ℚ := (22645835309898593/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell123Term01
