import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell220Term00
open CoupledFlow


def environment : Environment := ⟨(3/2), (123/80), (14711543064639738184203019540487037297311/5000000000000000000000000000000000000000), (19711543064639738184203019540487037297311/5000000000000000000000000000000000000000), 15, (978103817672969343012355296114718986119/312500000000000000000000000000000000000), (23886894551238303415339619738718281650929/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (3/5)

def qb : ℚ := (123/203)

def rho : ℚ := (153694545389548156854017550913/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (39204883257544696065617116551/250000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell220Term00
