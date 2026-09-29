import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell046Term00
open CoupledFlow


def environment : Environment := ⟨(8999/9625), (47/50), (1150515463917525773195876288659793814433/400000000000000000000000000000000000000), (1550515463917525773195876288659793814433/400000000000000000000000000000000000000), 4, (13823710526781111680021646712316056680951/10000000000000000000000000000000000000000), (18782017217557657561908810713146986927411/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (8999/18624)

def qb : ℚ := (47/97)

def rho : ℚ := (1/4)

def retention : ℚ := (7/10)

def rate : ℚ := (24782397444684564977108649539/200000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell046Term00
