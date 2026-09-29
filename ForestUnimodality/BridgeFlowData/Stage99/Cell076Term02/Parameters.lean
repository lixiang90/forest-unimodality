import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell076Term02
open CoupledFlow


def environment : Environment := ⟨(26/25), (3579/3425), (26463169975519307747800945400016795145991/10000000000000000000000000000000000000000), (36463169975519307747800945400016795145991/10000000000000000000000000000000000000000), 8, (1379212276670223862684609190272657353623/1000000000000000000000000000000000000000), (9316225395658452486392031952217312237829/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (26/51)

def qb : ℚ := (3579/7004)

def rho : ℚ := (70069842832997153862349067081/250000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (69535453542115233603889331417/250000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell076Term02
