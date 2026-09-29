import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell166Term00
open CoupledFlow


def environment : Environment := ⟨(23607/21125), (94453/84475), (26622558352085901756772031301284700092461/10000000000000000000000000000000000000000), (36622558352085901756772031301284700092461/10000000000000000000000000000000000000000), 10, (3707941314239019830776110718643353666137/2500000000000000000000000000000000000000), (4833103963646787644516773049075946439117/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (23607/44732)

def qb : ℚ := (94453/178928)

def rho : ℚ := (288282822135005366785868356573/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (12567285844209787483942431101/125000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell166Term00
