import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell167Term01
open CoupledFlow


def environment : Environment := ⟨(8069/7125), (12116/10675), (6695611436181315966783185293651138170557/2500000000000000000000000000000000000000), (9195611436181315966783185293651138170557/2500000000000000000000000000000000000000), 10, (14908674332486402711673359309139627201001/10000000000000000000000000000000000000000), (9777019714867520008208948533884181481679/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (8069/15194)

def qb : ℚ := (12116/22791)

def rho : ℚ := (289058188157916326639776585157/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (280346612514500966791355971229/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell167Term01
