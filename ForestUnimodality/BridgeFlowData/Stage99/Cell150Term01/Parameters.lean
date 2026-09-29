import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell150Term01
open CoupledFlow


def environment : Environment := ⟨(8069/7125), (12116/10675), (5433486026984757118118865782886029788273/2000000000000000000000000000000000000000), (7433486026984757118118865782886029788273/2000000000000000000000000000000000000000), 10, (7546909815614913299707050699854611328297/5000000000000000000000000000000000000000), (19758702273473589847555653070388999367013/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (8069/15194)

def qb : ℚ := (12116/22791)

def rho : ℚ := (14303204558924700934062167393/50000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (29171870096444499400838855007/200000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell150Term01
