import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell180Term00
open CoupledFlow


def environment : Environment := ⟨(236/135), (9/5), (776658205700623851336448376865299605661/250000000000000000000000000000000000000), (1026658205700623851336448376865299605661/250000000000000000000000000000000000000), 15, (16412449995968336272517124387578032311173/5000000000000000000000000000000000000000), (13199891216150878088611479131125280644213/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (236/371)

def qb : ℚ := (9/14)

def rho : ℚ := (7827058938500824172691332469/25000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (113168248075390483767713161463/1000000000000000000000000000000)

def finish : ℚ := (2231435513142097/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell180Term00
