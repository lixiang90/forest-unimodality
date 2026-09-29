import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell167Term00
open CoupledFlow


def environment : Environment := ⟨(53/40), (107/80), (14308839022934572772100614987516016267399/5000000000000000000000000000000000000000), (19308839022934572772100614987516016267399/5000000000000000000000000000000000000000), 14, (10039618691631557554795057961763885981633/5000000000000000000000000000000000000000), (11048373130770049661041528361840715190437/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (53/93)

def qb : ℚ := (107/187)

def rho : ℚ := (296337088257531955001424172497/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (4835836928903181707583186937/31250000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell167Term00
