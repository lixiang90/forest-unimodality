import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell215Term01
open CoupledFlow


def environment : Environment := ⟨(27/20), (653/475), (3561697450871294798160196234827663689889/1250000000000000000000000000000000000000), (4811697450871294798160196234827663689889/1250000000000000000000000000000000000000), 14, (20003435691833257338474087756542866855609/10000000000000000000000000000000000000000), (5570990133721552310635830037841248917549/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (27/47)

def qb : ℚ := (653/1128)

def rho : ℚ := (37597224987295784194032374477/125000000000000000000000000000)

def retention : ℚ := (3/10)

def rate : ℚ := (38582831105926099050621634537/200000000000000000000000000000)

def finish : ℚ := (120397280432593599262274621776183850293/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell215Term01
