import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell064Term01
open CoupledFlow


def environment : Environment := ⟨(9287/9725), (24/25), (12891252859430601421019190476755211035237/5000000000000000000000000000000000000000), (17891252859430601421019190476755211035237/5000000000000000000000000000000000000000), 4, (6287359330184332973961646308319534287443/5000000000000000000000000000000000000000), (17526125250054466698141247813964288361049/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (9287/19012)

def qb : ℚ := (24/49)

def rho : ℚ := (273762783532049947656716660123/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (268362034278857571725166571103/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell064Term01
