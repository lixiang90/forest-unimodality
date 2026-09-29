import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell169Term01
open CoupledFlow


def environment : Environment := ⟨(24257/21325), (32351/28425), (1673782990586315121687272752388756171729/625000000000000000000000000000000000000), (2298782990586315121687272752388756171729/625000000000000000000000000000000000000), 10, (14907751844449239470340641730127427445761/10000000000000000000000000000000000000000), (4894558939611549328794587390583694281401/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (24257/45582)

def qb : ℚ := (32351/60776)

def rho : ℚ := (289446054700170138552318729593/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (7320137910004111225625609529/50000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell169Term01
