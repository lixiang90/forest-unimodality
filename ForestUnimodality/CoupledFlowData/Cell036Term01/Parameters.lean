import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell036Term01
open CoupledFlow


def environment : Environment := ⟨(841/945), (1687/1885), (790411444467436632673166539807982385233/312500000000000000000000000000000000000), (1102911444467436632673166539807982385233/312500000000000000000000000000000000000), 3, (11801684641975065563339722192741664287661/10000000000000000000000000000000000000000), (16668413050988269646760420628497794256557/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (841/1786)

def qb : ℚ := (1687/3572)

def rho : ℚ := (3345438260674269060092143821/12500000000000000000000000000)

def retention : ℚ := (7/20)

def rate : ℚ := (231514115401964709987938518633/1000000000000000000000000000000)

def finish : ℚ := (104982212449867768832987083269936104601/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell036Term01
