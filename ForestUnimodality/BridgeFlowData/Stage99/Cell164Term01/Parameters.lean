import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell164Term01
open CoupledFlow


def environment : Environment := ⟨(116/91), (13/10), (14234555109837154618586742114911078987661/5000000000000000000000000000000000000000), (19234555109837154618586742114911078987661/5000000000000000000000000000000000000000), 13, (8786330654725191989466359351562443894343/5000000000000000000000000000000000000000), (2717926265520467500452474429280913335213/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (116/207)

def qb : ℚ := (13/23)

def rho : ℚ := (146927596733255849709379787199/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (74179849240001116299110309119/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell164Term01
