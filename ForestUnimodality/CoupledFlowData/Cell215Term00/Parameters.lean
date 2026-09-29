import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell215Term00
open CoupledFlow


def environment : Environment := ⟨(53/37), (107/73), (28985560015530162371665498737431211437671/10000000000000000000000000000000000000000), (38985560015530162371665498737431211437671/10000000000000000000000000000000000000000), 14, (20303909779337530102518541981784729885171/10000000000000000000000000000000000000000), (2896843695598421787339033586739680294327/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (53/90)

def qb : ℚ := (107/180)

def rho : ℚ := (152478108357977534849330037749/500000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (56853991972543197712623203151/1000000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell215Term00
