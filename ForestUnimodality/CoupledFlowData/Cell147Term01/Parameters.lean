import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell147Term01
open CoupledFlow


def environment : Environment := ⟨(22647/20825), (109/100), (26487971089515857938125708931235622755103/10000000000000000000000000000000000000000), (36487971089515857938125708931235622755103/10000000000000000000000000000000000000000), 9, (14331779898090280332296913265696660202063/10000000000000000000000000000000000000000), (9514805858270881615444263812212160000733/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (22647/43472)

def qb : ℚ := (109/209)

def rho : ℚ := (285864675346841191102524153151/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (71201217580684383887679096819/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell147Term01
