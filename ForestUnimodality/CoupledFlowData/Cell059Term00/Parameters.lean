import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell059Term00
open CoupledFlow


def environment : Environment := ⟨(9237/9775), (4631/4875), (25668638300651011197563800440808767096421/10000000000000000000000000000000000000000), (35668638300651011197563800440808767096421/10000000000000000000000000000000000000000), 4, (12526940689990858307921113255425413878481/10000000000000000000000000000000000000000), (4344136965345961310117766669508347370701/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (9237/19012)

def qb : ℚ := (4631/9506)

def rho : ℚ := (68290524061286535331421838563/250000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (18560095437838843651818191869/200000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell059Term00
