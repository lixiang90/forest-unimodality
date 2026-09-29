import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell090Term00
open CoupledFlow


def environment : Environment := ⟨(7339/6875), (107/100), (26651655076953753416808301772487058655443/10000000000000000000000000000000000000000), (36651655076953753416808301772487058655443/10000000000000000000000000000000000000000), 9, (14408202804604828168782578216571218834983/10000000000000000000000000000000000000000), (2368192689150997352414546068632919852737/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (7339/14214)

def qb : ℚ := (107/207)

def rho : ℚ := (35258176709556966722004201791/125000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (70257889819003563666137334101/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell090Term00
