import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell068Term02
open CoupledFlow


def environment : Environment := ⟨(51/50), (10429/10175), (26291688284691075441434274366229284830051/10000000000000000000000000000000000000000), (36291688284691075441434274366229284830051/10000000000000000000000000000000000000000), 7, (13591440861981278347328947646592341401881/10000000000000000000000000000000000000000), (18369540726123239457324696532974432706883/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (51/101)

def qb : ℚ := (10429/20604)

def rho : ℚ := (278942025352290208407290938451/1000000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (273976937457714663738462297851/1000000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell068Term02
