import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell223Term00
open CoupledFlow


def environment : Environment := ⟨(129/80), (33/20), (14971171126837337450098922851625488726429/5000000000000000000000000000000000000000), (19971171126837337450098922851625488726429/5000000000000000000000000000000000000000), 15, (31781556346397813907528532191212572777727/10000000000000000000000000000000000000000), (12434880135577964827420084039691342037211/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (129/209)

def qb : ℚ := (33/53)

def rho : ℚ := (77942538457002927288999007029/250000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (29321946715306331475542879421/500000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell223Term00
