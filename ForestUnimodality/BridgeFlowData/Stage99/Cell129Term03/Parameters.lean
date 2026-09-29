import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell129Term03
open CoupledFlow


def environment : Environment := ⟨(23607/21125), (94453/84475), (1688911109723063180996899942330827298657/625000000000000000000000000000000000000), (2313911109723063180996899942330827298657/625000000000000000000000000000000000000), 10, (15024164296356017005170965573346653606273/10000000000000000000000000000000000000000), (19543579186861529699964248435390649274797/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (23607/44732)

def qb : ℚ := (94453/178928)

def rho : ℚ := (142584000299049025095369333211/500000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (275777774515510137732979795297/1000000000000000000000000000000)

def finish : ℚ := (1141601776633929/500000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell129Term03
