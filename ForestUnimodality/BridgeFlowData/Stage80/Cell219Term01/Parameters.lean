import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell219Term01
open CoupledFlow


def environment : Environment := ⟨(107/73), (3/2), (73051172934113769971307686881141262823/25000000000000000000000000000000000000), (98051172934113769971307686881141262823/25000000000000000000000000000000000000), 14, (20447344934381792497632966863775490140871/10000000000000000000000000000000000000000), (294153518802341309913923060643423788469/125000000000000000000000000000000000000)⟩

def qa : ℚ := (107/180)

def qb : ℚ := (3/5)

def rho : ℚ := (152981341794650063753753516341/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (108167127462358294474360577077/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell219Term01
