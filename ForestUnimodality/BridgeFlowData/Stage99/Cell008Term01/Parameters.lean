import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell008Term01
open CoupledFlow


def environment : Environment := ⟨(13/29), (20/43), (15396825396825396825396825396825396825397/10000000000000000000000000000000000000000), (25396825396825396825396825396825396825397/10000000000000000000000000000000000000000), 0, (5319338024310997516383742507416877666989/10000000000000000000000000000000000000000), (4031242126480221718316956412194507432603/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (13/42)

def qb : ℚ := (20/63)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (193352433549996347728434978377/1000000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell008Term01
