import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell160Term00
open CoupledFlow


def environment : Environment := ⟨(2326/2105), (4657/4205), (13292030040070965207193559166331482712107/5000000000000000000000000000000000000000), (18292030040070965207193559166331482712107/5000000000000000000000000000000000000000), 10, (3703311331091234129369049450501950525997/2500000000000000000000000000000000000000), (19225002007810987354976394727512009702163/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2326/4431)

def qb : ℚ := (4657/8862)

def rho : ℚ := (143642379450060641160881088303/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (99807142772223361460760629077/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell160Term00
