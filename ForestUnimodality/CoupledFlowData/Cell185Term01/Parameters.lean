import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell185Term01
open CoupledFlow


def environment : Environment := ⟨(31933/28275), (113/100), (3335772598676002638836974154803566641951/1250000000000000000000000000000000000000), (4585772598676002638836974154803566641951/1250000000000000000000000000000000000000), 10, (297247402486496516786139007756520988387/200000000000000000000000000000000000000), (1946262173334791730285739265700668659307/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (31933/60208)

def qb : ℚ := (113/213)

def rho : ℚ := (289218676084185102572351289377/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (101183158985679019009309183557/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell185Term01
