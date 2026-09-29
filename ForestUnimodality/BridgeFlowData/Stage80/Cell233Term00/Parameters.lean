import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell233Term00
open CoupledFlow


def environment : Environment := ⟨(35/17), (53/25), (15870655591677163344445077165316602952443/5000000000000000000000000000000000000000), (20870655591677163344445077165316602952443/5000000000000000000000000000000000000000), 15, (33451144883261700195697228649065819071143/10000000000000000000000000000000000000000), (14181342902037046887892167817458717390763/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (35/52)

def qb : ℚ := (53/78)

def rho : ℚ := (162785298358846613522954646197/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (35530738256930955137600256957/250000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell233Term00
