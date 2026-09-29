import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell167Term00
open CoupledFlow


def environment : Environment := ⟨(94453/84475), (47239/42225), (6656485452072880843331684950408134034923/2500000000000000000000000000000000000000), (9156485452072880843331684950408134034923/2500000000000000000000000000000000000000), 10, (7416696435338694413980310224724602198927/5000000000000000000000000000000000000000), (19339319336066834398557876480923269412311/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (94453/178928)

def qb : ℚ := (47239/89464)

def rho : ℚ := (288332487145885765500683082233/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50282439637337384451434036731/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell167Term00
