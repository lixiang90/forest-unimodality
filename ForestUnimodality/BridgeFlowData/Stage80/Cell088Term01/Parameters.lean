import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell088Term01
open CoupledFlow


def environment : Environment := ⟨(405/403), (203/201), (26097783414593535550555709816862724900487/10000000000000000000000000000000000000000), (36097783414593535550555709816862724900487/10000000000000000000000000000000000000000), 6, (13198073247536896685453851548670070327607/10000000000000000000000000000000000000000), (18138242656342791378125765081245379096037/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (405/808)

def qb : ℚ := (203/404)

def rho : ℚ := (139198366213702984503926637907/500000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (33374824451334020841841297349/125000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell088Term01
