import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell122Term01
open CoupledFlow


def environment : Environment := ⟨(4657/4205), (111/100), (26973769060352942883610346623938196103011/10000000000000000000000000000000000000000), (36973769060352942883610346623938196103011/10000000000000000000000000000000000000000), 10, (15000691833229865724067355888956622526409/10000000000000000000000000000000000000000), (2431331970200934040332196964014893227153/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (4657/8862)

def qb : ℚ := (111/211)

def rho : ℚ := (142280964067307550970994171397/500000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (34453970157070250094711276821/125000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell122Term01
