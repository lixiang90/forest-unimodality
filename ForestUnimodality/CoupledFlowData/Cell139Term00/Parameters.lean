import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell139Term00
open CoupledFlow


def environment : Environment := ⟨(22331/20725), (27/25), (26432067191065794247306540806430470175073/10000000000000000000000000000000000000000), (36432067191065794247306540806430470175073/10000000000000000000000000000000000000000), 9, (2861135282724931600380600671665820832231/2000000000000000000000000000000000000000), (3783330054456832479527986929898548825873/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (22331/43056)

def qb : ℚ := (27/52)

def rho : ℚ := (285040520214071060750346477627/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (276316064746884524548519503/1953125000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell139Term00
