import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell174Term01
open CoupledFlow


def environment : Environment := ⟨(57/50), (29/25), (27083086107665617511465261538495612182027/10000000000000000000000000000000000000000), (37083086107665617511465261538495612182027/10000000000000000000000000000000000000000), 11, (15275099515313013151092836025387609055027/10000000000000000000000000000000000000000), (19914990687450053848749862678080976912571/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (57/107)

def qb : ℚ := (29/54)

def rho : ℚ := (57927976703753748141369002657/200000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (232257970022889324204549921379/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell174Term01
