import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell059Term00
open CoupledFlow


def environment : Environment := ⟨(4631/4875), (9287/9725), (6437294115366857615439125001226543080963/2500000000000000000000000000000000000000), (8937294115366857615439125001226543080963/2500000000000000000000000000000000000000), 4, (3140183608951157640857461579968125529089/2500000000000000000000000000000000000000), (3492558403089080861543578955875905979083/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (4631/9506)

def qb : ℚ := (9287/19012)

def rho : ℚ := (273282356543558688948847213939/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (93120119497609627965179075769/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell059Term00
