import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell131Term01
open CoupledFlow


def environment : Environment := ⟨(1549/1405), (2326/2105), (26621096513234553048318108282185082875079/10000000000000000000000000000000000000000), (36621096513234553048318108282185082875079/10000000000000000000000000000000000000000), 10, (14831062037082115208721600329319311078001/10000000000000000000000000000000000000000), (4805950715966123357616109222769267815811/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (1549/2954)

def qb : ℚ := (2326/4431)

def rho : ℚ := (286686083837224279994354368411/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (137181933386319477176314810941/500000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell131Term01
