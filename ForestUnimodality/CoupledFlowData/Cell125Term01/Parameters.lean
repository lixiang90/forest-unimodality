import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell125Term01
open CoupledFlow


def environment : Environment := ⟨(53/50), (21967/20675), (13166155769372347356933146083652864731863/5000000000000000000000000000000000000000), (18166155769372347356933146083652864731863/5000000000000000000000000000000000000000), 9, (3564773503414840836685712053731516808949/2500000000000000000000000000000000000000), (18716567880765552947317218705482973573699/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (53/103)

def qb : ℚ := (21967/42642)

def rho : ℚ := (141788221398418281696138323771/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (35160745987202293871178859889/200000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell125Term01
