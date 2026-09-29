import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell146Term00
open CoupledFlow


def environment : Environment := ⟨(22647/20825), (109/100), (26487971089515857938125708931235622755103/10000000000000000000000000000000000000000), (36487971089515857938125708931235622755103/10000000000000000000000000000000000000000), 9, (14331779898090280332296913265696660202063/10000000000000000000000000000000000000000), (9514805858270881615444263812212160000733/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (22647/43472)

def qb : ℚ := (109/209)

def rho : ℚ := (285864675346841191102524153151/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (49555882676063472966597600707/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell146Term00
