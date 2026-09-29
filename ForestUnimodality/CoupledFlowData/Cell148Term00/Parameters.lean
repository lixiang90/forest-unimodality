import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell148Term00
open CoupledFlow


def environment : Environment := ⟨(109/100), (4583/4195), (2650160357864339019888898308381950090089/1000000000000000000000000000000000000000), (3650160357864339019888898308381950090089/1000000000000000000000000000000000000000), 9, (3584536300443136912595032350974063676607/2500000000000000000000000000000000000000), (4764378252475582629343478283012781175347/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (109/209)

def qb : ℚ := (4583/8778)

def rho : ℚ := (286070010697670776708336816587/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (24805288153999522603902243847/250000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell148Term00
