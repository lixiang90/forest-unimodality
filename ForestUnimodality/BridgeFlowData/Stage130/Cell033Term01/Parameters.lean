import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell033Term01
open CoupledFlow


def environment : Environment := ⟨(1687/1885), (9/10), (5578947368421052631578947368421052631579/2000000000000000000000000000000000000000), (7578947368421052631578947368421052631579/2000000000000000000000000000000000000000), 3, (1284244391270483723602092927902536497343/1000000000000000000000000000000000000000), (1795013850415512465373961218836565096953/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (1687/3572)

def qb : ℚ := (9/19)

def rho : ℚ := (1/4)

def retention : ℚ := (1/20)

def rate : ℚ := (244011109729239118525967169703/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell033Term01
