import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell145Term01
open CoupledFlow


def environment : Environment := ⟨(11791/10575), (23607/21125), (26689113389438431598780970062822754315033/10000000000000000000000000000000000000000), (36689113389438431598780970062822754315033/10000000000000000000000000000000000000000), 10, (7431890390558192250680640180137291211289/5000000000000000000000000000000000000000), (9681211434593501908616005994288839769237/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (11791/22366)

def qb : ℚ := (23607/44732)

def rho : ℚ := (143841852260181434988101018231/500000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (1733205827053817546199319317/6250000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell145Term01
