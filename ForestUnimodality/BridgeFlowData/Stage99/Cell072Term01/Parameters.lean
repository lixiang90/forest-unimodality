import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell072Term01
open CoupledFlow


def environment : Environment := ⟨(5227/5075), (3493/3375), (1648648297643042848756958496894317015393/625000000000000000000000000000000000000), (2273648297643042848756958496894317015393/625000000000000000000000000000000000000), 8, (13753986859085663562348310267775265078487/10000000000000000000000000000000000000000), (4625424288682090081949945270618432926481/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (5227/10302)

def qb : ℚ := (3493/6868)

def rho : ℚ := (279611497887598029932674014249/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (88154695175628501411380323511/500000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell072Term01
