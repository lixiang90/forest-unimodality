import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell171Term01
open CoupledFlow


def environment : Environment := ⟨(48539/42625), (97103/85225), (26787158054996631256653931313389839193547/10000000000000000000000000000000000000000), (36787158054996631256653931313389839193547/10000000000000000000000000000000000000000), 10, (745547044975632657244942769888869285653/500000000000000000000000000000000000000), (19591853191031206862987948599908371480031/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (48539/91164)

def qb : ℚ := (97103/182328)

def rho : ℚ := (18096436127573990433857831343/62500000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (146478038844140101934133453883/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell171Term01
