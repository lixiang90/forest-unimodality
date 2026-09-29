import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell035Term00
open CoupledFlow


def environment : Environment := ⟨(9/10), (1733/1915), (26850672040345757598859748311190784705121/10000000000000000000000000000000000000000), (36850672040345757598859748311190784705121/10000000000000000000000000000000000000000), 4, (1627835968460290635547184857407463669087/1250000000000000000000000000000000000000), (17506089541096271359326738986648473106901/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (9/19)

def qb : ℚ := (1733/3648)

def rho : ℚ := (25782695308313092428528877817/100000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (32113055558149333323701688527/250000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell035Term00
