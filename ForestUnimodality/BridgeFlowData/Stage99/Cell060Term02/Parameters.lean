import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell060Term02
open CoupledFlow


def environment : Environment := ⟨1, (405/403), (26115955328326728742092769145831627184853/10000000000000000000000000000000000000000), (36115955328326728742092769145831627184853/10000000000000000000000000000000000000000), 6, (13205990110225325233788730609823793238797/10000000000000000000000000000000000000000), (2262834453584827527931245591593720453259/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (1/2)

def qb : ℚ := (405/808)

def rho : ℚ := (138785647286821705426356589147/500000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (53929849056590369821476649621/200000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell060Term02
