import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell090Term01
open CoupledFlow


def environment : Environment := ⟨(407/401), (51/50), (13079762884037891846020185586698348289931/5000000000000000000000000000000000000000), (18079762884037891846020185586698348289931/5000000000000000000000000000000000000000), 7, (3383132299763886408952131729911878890181/2500000000000000000000000000000000000000), (9129385218672598852940885791303126364223/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (407/808)

def qb : ℚ := (51/101)

def rho : ℚ := (279290441079463145605389141829/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (174375421438415096020508823411/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell090Term01
