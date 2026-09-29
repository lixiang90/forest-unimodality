import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell050Term00
open CoupledFlow


def environment : Environment := ⟨(9287/9725), (24/25), (26442526181243892050463184078607736982231/10000000000000000000000000000000000000000), (36442526181243892050463184078607736982231/10000000000000000000000000000000000000000), 4, (6425782984504809577548838274316466487843/5000000000000000000000000000000000000000), (17849400578568436922675845262991544644359/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (9287/19012)

def qb : ℚ := (24/49)

def rho : ℚ := (53760918321785643461009132249/200000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (46714045702240333779954271943/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell050Term00
