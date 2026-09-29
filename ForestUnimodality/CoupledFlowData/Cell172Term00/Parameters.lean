import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell172Term00
open CoupledFlow


def environment : Environment := ⟨(47737/42575), (31833/28375), (6660674094922507301999546556724570384443/2500000000000000000000000000000000000000), (9160674094922507301999546556724570384443/2500000000000000000000000000000000000000), 10, (2968290520392110732751076834400647390241/2000000000000000000000000000000000000000), (3874724135844647554405415433699352232899/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (47737/90312)

def qb : ℚ := (31833/60208)

def rho : ℚ := (288579807842872497182581893039/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (20139471957035076117677562067/200000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell172Term00
