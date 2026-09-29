import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell151Term01
open CoupledFlow


def environment : Environment := ⟨(12116/10675), (24257/21325), (27186578102250204083205020837829034524831/10000000000000000000000000000000000000000), (37186578102250204083205020837829034524831/10000000000000000000000000000000000000000), 10, (1887878344183476329986536392663280933577/1250000000000000000000000000000000000000), (9894638508910131197032865939002444939547/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (12116/22791)

def qb : ℚ := (24257/45582)

def rho : ℚ := (35776471338552171347625639853/125000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (146059422961543767048522748033/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell151Term01
