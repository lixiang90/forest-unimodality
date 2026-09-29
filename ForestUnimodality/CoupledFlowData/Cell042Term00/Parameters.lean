import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell042Term00
open CoupledFlow


def environment : Environment := ⟨(1733/1915), (869/955), (12698982254924743154182594005719605006583/5000000000000000000000000000000000000000), (17698982254924743154182594005719605006583/5000000000000000000000000000000000000000), 4, (124133483185659961838792959754553071949/100000000000000000000000000000000000000), (421612269175701803755062340761248266193/250000000000000000000000000000000000000)⟩

def qa : ℚ := (1733/3648)

def qb : ℚ := (869/1824)

def rho : ℚ := (134591196186980133748413716259/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (81642865347163149843712356871/500000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell042Term00
