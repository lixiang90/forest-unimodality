import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell133Term00
open CoupledFlow


def environment : Environment := ⟨(28/25), (95449/85175), (27042073835186682632738249738579960379349/10000000000000000000000000000000000000000), (37042073835186682632738249738579960379349/10000000000000000000000000000000000000000), 10, (15033539855376281202011165434236177380831/10000000000000000000000000000000000000000), (19574524456853649961313187612375535024407/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (28/53)

def qb : ℚ := (95449/180624)

def rho : ℚ := (285318958228120754409444691657/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (25161017994383131378685153593/250000000000000000000000000000)

def finish : ℚ := (2231435513142097/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell133Term00
