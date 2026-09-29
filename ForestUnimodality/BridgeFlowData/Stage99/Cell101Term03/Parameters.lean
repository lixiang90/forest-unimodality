import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell101Term03
open CoupledFlow


def environment : Environment := ⟨(27/25), (22597/20875), (1672108022288299974363240818557283298567/625000000000000000000000000000000000000), (2297108022288299974363240818557283298567/625000000000000000000000000000000000000), 9, (14455854973002671400341376034218147154523/10000000000000000000000000000000000000000), (4776200771038711310331813836670862228351/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (27/52)

def qb : ℚ := (22597/43472)

def rho : ℚ := (56571768393033759390150104547/200000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (136251964356436494187285838821/500000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell101Term03
