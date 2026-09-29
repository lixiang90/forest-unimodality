import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell234Term00
open CoupledFlow


def environment : Environment := ⟨(53/25), (107/49), (15967937852211055653792336525635028247993/5000000000000000000000000000000000000000), (20967937852211055653792336525635028247993/5000000000000000000000000000000000000000), 15, (16815809880222168499027286342522027940621/5000000000000000000000000000000000000000), (1438185480888835227535756415540351296497/500000000000000000000000000000000000000)⟩

def qa : ℚ := (53/78)

def qb : ℚ := (107/156)

def rho : ℚ := (163558629544752406570016425253/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (73085112250887904163599176111/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell234Term00
