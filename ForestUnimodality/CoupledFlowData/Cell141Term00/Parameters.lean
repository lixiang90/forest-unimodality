import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell141Term00
open CoupledFlow


def environment : Environment := ⟨(27/25), (22597/20875), (26445867072182666586948919985955829463983/10000000000000000000000000000000000000000), (36445867072182666586948919985955829463983/10000000000000000000000000000000000000000), 9, (14312120172321361529438970808214144768897/10000000000000000000000000000000000000000), (1184048436680667609129561477679086363633/625000000000000000000000000000000000000)⟩

def qa : ℚ := (27/52)

def qb : ℚ := (22597/43472)

def rho : ℚ := (17828010889862884013025818133/62500000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (3541646337154634487314300739/25000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell141Term00
