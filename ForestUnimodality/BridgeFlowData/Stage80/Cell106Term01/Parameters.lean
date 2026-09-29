import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell106Term01
open CoupledFlow


def environment : Environment := ⟨(7427/6925), (11153/10375), (13226871762676318696149760780880682340651/5000000000000000000000000000000000000000), (18226871762676318696149760780880682340651/5000000000000000000000000000000000000000), 9, (3578949498642485826045297548391425068501/2500000000000000000000000000000000000000), (9442786174708704125704119378909431909387/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (7427/14352)

def qb : ℚ := (11153/21528)

def rho : ℚ := (71058475864800263606622675247/250000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (6707812420856697109111224987/25000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell106Term01
