import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell032Term00
open CoupledFlow


def environment : Environment := ⟨(22/25), (1677/1895), (12610546471633308717870319842674444207011/5000000000000000000000000000000000000000), (17610546471633308717870319842674444207011/5000000000000000000000000000000000000000), 3, (11772818839021281580887525166260342831513/10000000000000000000000000000000000000000), (8267885339565805912617168638344076969529/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (22/47)

def qb : ℚ := (1677/3572)

def rho : ℚ := (66648255801580204885740793509/250000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (22344469923912286296074566451/250000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell032Term00
