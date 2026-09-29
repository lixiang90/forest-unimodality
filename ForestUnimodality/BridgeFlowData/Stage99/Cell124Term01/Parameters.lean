import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell124Term01
open CoupledFlow


def environment : Environment := ⟨(111/100), (23557/21175), (2699319577689531976800381411805606838387/1000000000000000000000000000000000000000), (3699319577689531976800381411805606838387/1000000000000000000000000000000000000000), 10, (7505017196253301025740915363634035920933/5000000000000000000000000000000000000000), (19481550409468010546697349753622614748253/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (111/211)

def qb : ℚ := (23557/44732)

def rho : ℚ := (3558933093448772864348059149/12500000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (275881969640492748923777771137/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell124Term01
