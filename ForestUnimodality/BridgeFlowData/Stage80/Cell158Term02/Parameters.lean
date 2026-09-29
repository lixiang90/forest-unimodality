import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell158Term02
open CoupledFlow


def environment : Environment := ⟨(11953/10625), (31883/28325), (26713941336671220186945131188865534773723/10000000000000000000000000000000000000000), (36713941336671220186945131188865534773723/10000000000000000000000000000000000000000), 10, (297514470704032435807031806754631735957/200000000000000000000000000000000000000), (9720889181147758713297000545563711177839/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (11953/22578)

def qb : ℚ := (31883/60208)

def rho : ℚ := (288472198380135895053186570321/1000000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (13983340770644513650909127953/50000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell158Term02
