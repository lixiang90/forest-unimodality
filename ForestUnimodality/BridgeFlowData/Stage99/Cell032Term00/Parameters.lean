import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell032Term00
open CoupledFlow


def environment : Environment := ⟨(841/945), (1687/1885), (5385333562266014513503791142544253519111/2000000000000000000000000000000000000000), (7385333562266014513503791142544253519111/2000000000000000000000000000000000000000), 3, (2491084487835781606886900222342508430413/2000000000000000000000000000000000000000), (4359972606222972593883292153370715175931/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (841/1786)

def qb : ℚ := (1687/3572)

def rho : ℚ := (51159171675443971802090613599/200000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (44992349931850419384182078821/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell032Term00
