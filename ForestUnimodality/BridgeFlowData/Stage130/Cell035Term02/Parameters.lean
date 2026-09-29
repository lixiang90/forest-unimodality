import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell035Term02
open CoupledFlow


def environment : Environment := ⟨(1733/1915), (869/955), (5622807017543859649122807017543859649123/2000000000000000000000000000000000000000), (7622807017543859649122807017543859649123/2000000000000000000000000000000000000000), 4, (2710406266631241726323556455061176420241/2000000000000000000000000000000000000000), (18158495883348722683902739304401354262851/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (1733/3648)

def qb : ℚ := (869/1824)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (3026441361127899698035053369/12500000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell035Term02
