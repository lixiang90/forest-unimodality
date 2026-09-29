import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell185Term00
open CoupledFlow


def environment : Environment := ⟨(35/17), (53/25), (8049439166899161294558473256559742562847/2500000000000000000000000000000000000000), (10549439166899161294558473256559742562847/2500000000000000000000000000000000000000), 15, (6774901661100561713718352894884685842241/2000000000000000000000000000000000000000), (28672834658751566595466619620393146452867/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (35/52)

def qb : ℚ := (53/78)

def rho : ℚ := (322048958592603488299797111261/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (141841878702201082765048635717/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell185Term00
