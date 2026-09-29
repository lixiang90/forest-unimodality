import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell083Term01
open CoupledFlow


def environment : Environment := ⟨(395/397), 1, (13018522081624897071636924436434048482657/5000000000000000000000000000000000000000), (18018522081624897071636924436434048482657/5000000000000000000000000000000000000000), 5, (13079715446812102045719692459700566522681/10000000000000000000000000000000000000000), (18018522081624897071636924436434048482657/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (395/792)

def qb : ℚ := (1/2)

def rho : ℚ := (138746118503774191803317290713/500000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (280065252093933762142925341949/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell083Term01
