import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell075Term01
open CoupledFlow


def environment : Environment := ⟨(4777/4925), (3193/3275), (25831157155331994651567409989801307185759/10000000000000000000000000000000000000000), (35831157155331994651567409989801307185759/10000000000000000000000000000000000000000), 5, (12990630281185336865045702212360102021121/10000000000000000000000000000000000000000), (8844224242190403441748201924662613933529/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (4777/9702)

def qb : ℚ := (3193/6468)

def rho : ℚ := (2152722745353484154092563887/7812500000000000000000000000)

def retention : ℚ := (2/5)

def rate : ℚ := (228669448724342808047974414263/1000000000000000000000000000000)

def finish : ℚ := (91629073187415506518352721176801107143/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell075Term01
