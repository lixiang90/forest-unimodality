import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell139Term01
open CoupledFlow


def environment : Environment := ⟨(4657/4205), (111/100), (6662145678989078334997174570960769206181/2500000000000000000000000000000000000000), (9162145678989078334997174570960769206181/2500000000000000000000000000000000000000), 10, (7422142089323327751518070239007642596833/5000000000000000000000000000000000000000), (963979308405485966999702727371227850129/500000000000000000000000000000000000000)⟩

def qa : ℚ := (4657/8862)

def qb : ℚ := (111/211)

def rho : ℚ := (57417374613164297762800940383/200000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (17228007393845987226637753711/62500000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell139Term01
