import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell192Term01
open CoupledFlow


def environment : Environment := ⟨(97103/85225), (57/50), (13369506075903427967174671712118345233627/5000000000000000000000000000000000000000), (18369506075903427967174671712118345233627/5000000000000000000000000000000000000000), 10, (14887782871924048674878014048444096647083/10000000000000000000000000000000000000000), (19571249464046642880915070796088704267603/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (97103/182328)

def qb : ℚ := (57/107)

def rho : ℚ := (144998531308532374358971026539/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50864395669445288048891156783/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell192Term01
