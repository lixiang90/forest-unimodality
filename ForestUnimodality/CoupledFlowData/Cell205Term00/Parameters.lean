import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell205Term00
open CoupledFlow


def environment : Environment := ⟨(99/80), (5/4), (2759634253074823001227541031879553654067/1000000000000000000000000000000000000000), (3759634253074823001227541031879553654067/1000000000000000000000000000000000000000), 13, (3420763731913546220454153056564114945467/2000000000000000000000000000000000000000), (417737139230535889025282336875505961563/200000000000000000000000000000000000000)⟩

def qa : ℚ := (99/179)

def qb : ℚ := (5/9)

def rho : ℚ := (295537022039414360061761089997/1000000000000000000000000000000)

def retention : ℚ := (19/20)

def rate : ℚ := (27308240722119234678127301101/1000000000000000000000000000000)

def finish : ℚ := (5129329438755053342619614425468723841/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell205Term00
