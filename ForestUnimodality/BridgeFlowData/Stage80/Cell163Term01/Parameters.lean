import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell163Term01
open CoupledFlow


def environment : Environment := ⟨(95749/84875), (47887/42425), (26730725411326789636445817126960667523279/10000000000000000000000000000000000000000), (36730725411326789636445817126960667523279/10000000000000000000000000000000000000000), 10, (148837968858247007974646030787200915799/100000000000000000000000000000000000000), (3895217131216684328373817089110562241313/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (95749/180624)

def qb : ℚ := (47887/90312)

def rho : ℚ := (288717202203589996920619347801/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (279937638476254780433839177933/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell163Term01
