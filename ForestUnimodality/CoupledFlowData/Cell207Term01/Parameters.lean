import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell207Term01
open CoupledFlow


def environment : Environment := ⟨(116/91), (13/10), (5599952443001765361331539713117746393193/2000000000000000000000000000000000000000), (7599952443001765361331539713117746393193/2000000000000000000000000000000000000000), 13, (8660284045193688198919578211618609383959/5000000000000000000000000000000000000000), (4295625293870563030317826794370900135283/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (116/207)

def qb : ℚ := (13/23)

def rho : ℚ := (7437117475975981368267286399/25000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (52225844386851617075104112079/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell207Term01
