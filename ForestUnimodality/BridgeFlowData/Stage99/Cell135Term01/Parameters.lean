import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell135Term01
open CoupledFlow


def environment : Environment := ⟨(47737/42575), (31833/28375), (27051772082946374921780360096643470039379/10000000000000000000000000000000000000000), (37051772082946374921780360096643470039379/10000000000000000000000000000000000000000), 10, (15038203637116779918943630027940762824337/10000000000000000000000000000000000000000), (4897476501114602514969083024500280617873/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (47737/90312)

def qb : ℚ := (31833/60208)

def rho : ℚ := (570787397505484790992579607/2000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (5795657539490990969709596287/40000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell135Term01
