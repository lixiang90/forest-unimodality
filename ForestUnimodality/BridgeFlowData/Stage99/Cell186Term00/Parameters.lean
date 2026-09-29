import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell186Term00
open CoupledFlow


def environment : Environment := ⟨(53/25), (107/49), (1012326524109245677053630137025411739603/312500000000000000000000000000000000000), (1324826524109245677053630137025411739603/312500000000000000000000000000000000000), 15, (34056914961929189892908166564370555464301/10000000000000000000000000000000000000000), (7269560927163553202294278187780464417309/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (53/78)

def qb : ℚ := (107/156)

def rho : ℚ := (161789445498959470134410389021/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (145947946163619422440001104877/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell186Term00
