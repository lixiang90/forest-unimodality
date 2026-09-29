import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell172Term02
open CoupledFlow


def environment : Environment := ⟨(53/37), (107/73), (14733541972281116850537349279932536905821/5000000000000000000000000000000000000000), (19733541972281116850537349279932536905821/5000000000000000000000000000000000000000), 14, (20597904415547455328556379729731951694507/10000000000000000000000000000000000000000), (23460988789267550033416626366142016099143/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (53/90)

def qb : ℚ := (107/180)

def rho : ℚ := (30123555379943233509091166549/100000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (170510472745892339151300297163/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell172Term02
