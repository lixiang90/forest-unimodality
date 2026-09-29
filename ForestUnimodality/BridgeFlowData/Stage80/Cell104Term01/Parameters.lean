import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell104Term01
open CoupledFlow


def environment : Environment := ⟨(7339/6875), (107/100), (13212722649446437161110362839647009082773/5000000000000000000000000000000000000000), (18212722649446437161110362839647009082773/5000000000000000000000000000000000000000), 9, (14302584340968589865734965009069776626861/10000000000000000000000000000000000000000), (18828611821166848079602017621664057699099/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (7339/14214)

def qb : ℚ := (107/207)

def rho : ℚ := (283817100007338844195543902303/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (44204569544833196455673213243/250000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell104Term01
