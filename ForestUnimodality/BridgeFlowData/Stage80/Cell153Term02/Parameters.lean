import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell153Term02
open CoupledFlow


def environment : Environment := ⟨(31833/28375), (23881/21275), (1067885721820370803875911805448120774977/400000000000000000000000000000000000000), (1467885721820370803875911805448120774977/400000000000000000000000000000000000000), 10, (371691080930254774634899688988496571927/250000000000000000000000000000000000000), (2425935847588933029896404258702233107673/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (31833/60208)

def qb : ℚ := (23881/45156)

def rho : ℚ := (5764541642053279989518106277/20000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (17437759272022390545939063519/62500000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell153Term02
