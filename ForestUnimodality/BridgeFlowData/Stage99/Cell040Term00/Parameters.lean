import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell040Term00
open CoupledFlow


def environment : Environment := ⟨(581/635), (23/25), (13370332880630602825184820449854562862329/5000000000000000000000000000000000000000), (18370332880630602825184820449854562862329/5000000000000000000000000000000000000000), 4, (3244142843584422487220146713545016046749/2500000000000000000000000000000000000000), (4401225585984415260200529899444322352433/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (581/1216)

def qb : ℚ := (23/48)

def rho : ℚ := (260837225857726644261408350881/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (164975113033072807762370612241/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell040Term00
