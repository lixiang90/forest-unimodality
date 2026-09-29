import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell101Term01
open CoupledFlow


def environment : Environment := ⟨(10996/10325), (7339/6875), (26411013643784292975770772780454850622173/10000000000000000000000000000000000000000), (36411013643784292975770772780454850622173/10000000000000000000000000000000000000000), 9, (14295845464328661694147349609783889278589/10000000000000000000000000000000000000000), (2349975632578205696401274284470927859119/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (10996/21321)

def qb : ℚ := (7339/14214)

def rho : ℚ := (17725472475532827424636150599/62500000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (266846955397491257238438880189/1000000000000000000000000000000)

def finish : ℚ := (11184338897989661/5000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell101Term01
