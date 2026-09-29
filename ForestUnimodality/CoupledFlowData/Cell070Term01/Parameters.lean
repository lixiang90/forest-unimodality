import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell070Term01
open CoupledFlow


def environment : Environment := ⟨(9529/9875), (4777/4925), (25798759963703199808281761772075125180179/10000000000000000000000000000000000000000), (35798759963703199808281761772075125180179/10000000000000000000000000000000000000000), 5, (3244152724656732226945983802323862566777/2500000000000000000000000000000000000000), (8813166169171829802317149865244427591513/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (9529/19404)

def qb : ℚ := (4777/9702)

def rho : ℚ := (137539039664402802851605377441/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (171939869203348460605047412077/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell070Term01
