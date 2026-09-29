import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell023Term00
open CoupledFlow


def environment : Environment := ⟨(65/88), (22/29), (24491796472260375074188903710021635768069/10000000000000000000000000000000000000000), (34491796472260375074188903710021635768069/10000000000000000000000000000000000000000), 2, (2753895439917542593873577283695886867369/2500000000000000000000000000000000000000), (14878814164504475522199134933734823272501/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (65/153)

def qb : ℚ := (22/51)

def rho : ℚ := (62532629949636601738437586637/250000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (14203834370183268091371285439/125000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell023Term00
