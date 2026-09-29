import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell156Term00
open CoupledFlow


def environment : Environment := ⟨(57/50), (29/25), (27488593426811906539893435066144429364053/10000000000000000000000000000000000000000), (37488593426811906539893435066144429364053/10000000000000000000000000000000000000000), 11, (7736470511181881648169484650091435401471/5000000000000000000000000000000000000000), (20132763136621209067720548461447934288103/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (57/107)

def qb : ℚ := (29/54)

def rho : ℚ := (71626725351203390824210120701/250000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50411992347801539931759495151/500000000000000000000000000000)

def finish : ℚ := (2231435513142097/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell156Term00
