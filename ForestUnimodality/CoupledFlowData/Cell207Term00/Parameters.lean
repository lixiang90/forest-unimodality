import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell207Term00
open CoupledFlow


def environment : Environment := ⟨(116/91), (13/10), (5599952443001765361331539713117746393193/2000000000000000000000000000000000000000), (7599952443001765361331539713117746393193/2000000000000000000000000000000000000000), 13, (8660284045193688198919578211618609383959/5000000000000000000000000000000000000000), (4295625293870563030317826794370900135283/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (116/207)

def qb : ℚ := (13/23)

def rho : ℚ := (7437117475975981368267286399/25000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (2727656715948120196610291127/50000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell207Term00
