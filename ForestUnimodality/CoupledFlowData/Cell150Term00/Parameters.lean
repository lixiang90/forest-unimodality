import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell150Term00
open CoupledFlow


def environment : Environment := ⟨(4583/4195), (2294/2095), (26515476306181512349760549899891922476487/10000000000000000000000000000000000000000), (36515476306181512349760549899891922476487/10000000000000000000000000000000000000000), 9, (143446226048770338299250780944299642977/100000000000000000000000000000000000000), (4771388849759648515057570145269541476479/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (4583/8778)

def qb : ℚ := (2294/4389)

def rho : ℚ := (286273309301194164995767912653/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (99329425026072352967723998893/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell150Term00
