import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell215Term00
open CoupledFlow


def environment : Environment := ⟨(27/20), (653/475), (3561697450871294798160196234827663689889/1250000000000000000000000000000000000000), (4811697450871294798160196234827663689889/1250000000000000000000000000000000000000), 14, (20003435691833257338474087756542866855609/10000000000000000000000000000000000000000), (5570990133721552310635830037841248917549/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (27/47)

def qb : ℚ := (653/1128)

def rho : ℚ := (37597224987295784194032374477/125000000000000000000000000000)

def retention : ℚ := (7/20)

def rate : ℚ := (38055648276910244727634239647/200000000000000000000000000000)

def finish : ℚ := (104982212449867768832987083269936104601/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell215Term00
