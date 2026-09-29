import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02
open CoupledFlow


def environment : Environment := ⟨(67/86), (4/5), (6388888888888888888888888888888888888889/2500000000000000000000000000000000000000), (8888888888888888888888888888888888888889/2500000000000000000000000000000000000000), 2, (1428057257558042569280814915439579050483/1250000000000000000000000000000000000000), (15802469135802469135802469135802469135803/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (67/153)

def qb : ℚ := (4/9)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (121547921590494897924328273029/500000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02
