import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell171Term00
open CoupledFlow


def environment : Environment := ⟨(7/5), (53/37), (29283973560991393703254369498610286922753/10000000000000000000000000000000000000000), (39283973560991393703254369498610286922753/10000000000000000000000000000000000000000), 14, (20486116904567107612650937315073491489791/10000000000000000000000000000000000000000), (722934235671022175789056105356369863509/312500000000000000000000000000000000000)⟩

def qa : ℚ := (7/12)

def qb : ℚ := (53/90)

def rho : ℚ := (299811264242194617194506993921/1000000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (56113484299004005576341913251/1000000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell171Term00
