import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell135Term00
open CoupledFlow


def environment : Environment := ⟨(2326/2105), (4657/4205), (13317422159509304710322592789331456298103/5000000000000000000000000000000000000000), (18317422159509304710322592789331456298103/5000000000000000000000000000000000000000), 10, (741883770385147219193759836086212462223/500000000000000000000000000000000000000), (19251689234221356812451436384544480248311/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2326/4431)

def qb : ℚ := (4657/8862)

def rho : ℚ := (14344325839341623113989393853/50000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (143500979368376173714454089903/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell135Term00
