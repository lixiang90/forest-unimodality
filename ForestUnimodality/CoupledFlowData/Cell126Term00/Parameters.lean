import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell126Term00
open CoupledFlow


def environment : Environment := ⟨(21967/20675), (10996/10325), (6586676932940921362959618649036828995977/2500000000000000000000000000000000000000), (9086676932940921362959618649036828995977/2500000000000000000000000000000000000000), 9, (1783227096324325873725292757807723916277/1250000000000000000000000000000000000000), (9372646644586874096628110000920123037359/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (21967/42642)

def qb : ℚ := (10996/21321)

def rho : ℚ := (283786726151015803777334043179/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (97719315156794242671909294063/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell126Term00
