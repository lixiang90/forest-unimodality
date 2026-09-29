import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell173Term03
open CoupledFlow


def environment : Environment := ⟨(107/73), (3/2), (3706168624257479391277273091551221018999/1250000000000000000000000000000000000000), (4956168624257479391277273091551221018999/1250000000000000000000000000000000000000), 14, (20709163178312291503202435553223261099741/10000000000000000000000000000000000000000), (5947402349108975269532727709861465222799/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (107/180)

def qb : ℚ := (3/5)

def rho : ℚ := (37831642588248452560188442083/125000000000000000000000000000)

def retention : ℚ := (1/4)

def rate : ℚ := (8575474411775827674460644793/40000000000000000000000000000)

def finish : ℚ := (138629436111989061883446424291635313613/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell173Term03
