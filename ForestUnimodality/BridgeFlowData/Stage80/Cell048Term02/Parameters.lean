import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell048Term02
open CoupledFlow


def environment : Environment := ⟨(47/50), (9237/9775), (25682374675413415680823171625483777142813/10000000000000000000000000000000000000000), (35682374675413415680823171625483777142813/10000000000000000000000000000000000000000), 4, (3133176158093863133009707114161921362351/2500000000000000000000000000000000000000), (17336318897369751769606755538848813879033/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (47/97)

def qb : ℚ := (9237/19012)

def rho : ℚ := (272319903519357219949881759029/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (267722541360795481407824105701/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell048Term02
