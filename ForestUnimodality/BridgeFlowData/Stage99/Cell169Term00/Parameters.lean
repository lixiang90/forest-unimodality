import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell169Term00
open CoupledFlow


def environment : Environment := ⟨(27/20), (653/475), (7228627704006180830003216681020153127259/2500000000000000000000000000000000000000), (9728627704006180830003216681020153127259/2500000000000000000000000000000000000000), 14, (5065130738168736685794749471464947266357/2500000000000000000000000000000000000000), (2815954738792569185280186388610886521321/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (27/47)

def qb : ℚ := (653/1128)

def rho : ℚ := (297524340962020210612074075453/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (1075881573005908261334822601/8000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell169Term00
