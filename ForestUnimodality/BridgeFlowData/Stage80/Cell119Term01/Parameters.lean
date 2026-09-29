import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell119Term01
open CoupledFlow


def environment : Environment := ⟨(109/100), (4583/4195), (26552067763787462982637312888885742784973/10000000000000000000000000000000000000000), (36552067763787462982637312888885742784973/10000000000000000000000000000000000000000), 9, (574468296049616624665025331539596098683/400000000000000000000000000000000000000), (19083860396609471730397220889697352379077/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (109/209)

def qb : ℚ := (4583/8778)

def rho : ℚ := (11427002372292241371411676943/40000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (33945686087532882696621968341/125000000000000000000000000000)

def finish : ℚ := (5650043237988647/2500000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell119Term01
