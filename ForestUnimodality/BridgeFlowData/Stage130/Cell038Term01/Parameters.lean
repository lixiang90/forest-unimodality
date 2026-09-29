import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell038Term01
open CoupledFlow


def environment : Environment := ⟨(581/635), (23/25), (14166666666666666666666666666666666666667/5000000000000000000000000000000000000000), (19166666666666666666666666666666666666667/5000000000000000000000000000000000000000), 4, (1705483344245847509121015198334001539467/1250000000000000000000000000000000000000), (4592013888888888888888888888888888888889/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (581/1216)

def qb : ℚ := (23/48)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (7588669204709574723135444063/31250000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell038Term01
