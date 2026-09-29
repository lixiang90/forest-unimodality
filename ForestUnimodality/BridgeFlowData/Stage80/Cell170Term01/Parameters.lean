import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell170Term01
open CoupledFlow


def environment : Environment := ⟨(32351/28425), (48539/42625), (5356768638845065094414408286946535657167/2000000000000000000000000000000000000000), (7356768638845065094414408286946535657167/2000000000000000000000000000000000000000), 10, (14909346490507900069706349639212194438067/10000000000000000000000000000000000000000), (19585044149055581952184028993906470441361/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (32351/60776)

def qb : ℚ := (48539/91164)

def rho : ℚ := (72373629708341618253052132407/250000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (73220199274554483588950340107/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell170Term01
