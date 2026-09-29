import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell226Term00
open CoupledFlow


def environment : Environment := ⟨(83/43), 2, (3133939837553642585391060556991869918631/1000000000000000000000000000000000000000), (4133939837553642585391060556991869918631/1000000000000000000000000000000000000000), 15, (33078279678774905989266880068909408298639/10000000000000000000000000000000000000000), (1377979945851214195130353518997289972877/500000000000000000000000000000000000000)⟩

def qa : ℚ := (83/126)

def qb : ℚ := (2/3)

def rho : ℚ := (322533318269664298728825115413/1000000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (31260542780823687412379331221/500000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell226Term00
