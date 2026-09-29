import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell214Term00
open CoupledFlow


def environment : Environment := ⟨(7/5), (53/37), (14402341848485374708765377175511712335211/5000000000000000000000000000000000000000), (19402341848485374708765377175511712335211/5000000000000000000000000000000000000000), 14, (20193452065566570148916013948790142553721/10000000000000000000000000000000000000000), (571291176649847144202536105723400418759/250000000000000000000000000000000000000)⟩

def qa : ℚ := (7/12)

def qb : ℚ := (53/90)

def rho : ℚ := (37939291909165847532382633611/125000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (28059139813600300717505621497/500000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell214Term00
