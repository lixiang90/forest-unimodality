import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell147Term02
open CoupledFlow


def environment : Environment := ⟨(47887/42425), (31933/28275), (5421981668904283585200637739763641882871/2000000000000000000000000000000000000000), (7421981668904283585200637739763641882871/2000000000000000000000000000000000000000), 10, (15066159995491083019407518058787121680679/10000000000000000000000000000000000000000), (9841139908032175447042418156385877966621/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (47887/90312)

def qb : ℚ := (31933/60208)

def rho : ℚ := (285841731502096871110114032179/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (91940462437892190921349485671/500000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell147Term02
