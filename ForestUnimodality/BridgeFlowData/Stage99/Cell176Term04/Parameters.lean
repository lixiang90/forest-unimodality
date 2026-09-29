import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell176Term04
open CoupledFlow


def environment : Environment := ⟨(63/40), (129/80), (30209827382520393147212887518737423178033/10000000000000000000000000000000000000000), (40209827382520393147212887518737423178033/10000000000000000000000000000000000000000), 15, (16014955710333429702594368031142660305197/5000000000000000000000000000000000000000), (24818505896388185243973504736445586554863/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (63/103)

def qb : ℚ := (129/209)

def rho : ℚ := (307002004515487592823957125089/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (100015340141243264096997746881/500000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell176Term04
