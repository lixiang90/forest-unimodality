import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell236Term00
open CoupledFlow


def environment : Environment := ⟨(9/5), (41/22), (15765578419374018444476307267867535033873/5000000000000000000000000000000000000000), (20765578419374018444476307267867535033873/5000000000000000000000000000000000000000), 15, (16628094435483056224584753139246949848853/5000000000000000000000000000000000000000), (6757053295193132985901020618909277272927/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (9/14)

def qb : ℚ := (41/63)

def rho : ℚ := (313400203765318023034505606997/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (115176453448796176308624641393/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell236Term00
