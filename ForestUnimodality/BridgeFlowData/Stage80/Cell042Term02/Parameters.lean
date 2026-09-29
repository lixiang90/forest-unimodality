import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell042Term02
open CoupledFlow


def environment : Environment := ⟨(23/25), (2983/3225), (25547422281784634598801980382964607300607/10000000000000000000000000000000000000000), (35547422281784634598801980382964607300607/10000000000000000000000000000000000000000), 4, (1247607397388050107578311682245229205979/1000000000000000000000000000000000000000), (533776783316706089965701048457551866431/312500000000000000000000000000000000000)⟩

def qa : ℚ := (23/48)

def qb : ℚ := (2983/6208)

def rho : ℚ := (270348165787976830207185402471/1000000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (133034362464791732836652824741/500000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell042Term02
