import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell116Term00
open CoupledFlow


def environment : Environment := ⟨(26/25), (3579/3425), (6564476291130894853390153627696752573989/2500000000000000000000000000000000000000), (9064476291130894853390153627696752573989/2500000000000000000000000000000000000000), 8, (13699804263252969325151912370295307364561/10000000000000000000000000000000000000000), (1157972610149824124795950879266371982521/625000000000000000000000000000000000000)⟩

def qa : ℚ := (26/51)

def qb : ℚ := (3579/7004)

def rho : ℚ := (17616631309669530073104738771/62500000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (140241769143476673945265095559/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell116Term00
