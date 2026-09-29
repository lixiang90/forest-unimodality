import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell166Term02
open CoupledFlow


def environment : Environment := ⟨(113/100), (8069/7125), (5353835958091562374727380806987498790189/2000000000000000000000000000000000000000), (7353835958091562374727380806987498790189/2000000000000000000000000000000000000000), 10, (745114675764738341830470189806239051339/500000000000000000000000000000000000000), (24408525711564111162990010749137047411/12500000000000000000000000000000000000)⟩

def qa : ℚ := (113/213)

def qb : ℚ := (8069/15194)

def rho : ℚ := (72216037597735552297503272163/250000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (1750637480082160019180667179/6250000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell166Term02
