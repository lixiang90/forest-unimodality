import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell102Term00
open CoupledFlow


def environment : Environment := ⟨(22597/20875), (11311/10425), (26774031319260309764593132787860163648451/10000000000000000000000000000000000000000), (36774031319260309764593132787860163648451/10000000000000000000000000000000000000000), 9, (14465332797911202032337431727761237920651/10000000000000000000000000000000000000000), (3827300959257944090424300008865350671951/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (22597/43472)

def qb : ℚ := (11311/21736)

def rho : ℚ := (283015441161095009944747266327/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (141945010051311145193411320549/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell102Term00
