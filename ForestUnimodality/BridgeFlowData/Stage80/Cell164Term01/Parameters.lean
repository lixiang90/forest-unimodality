import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell164Term01
open CoupledFlow


def environment : Environment := ⟨(47887/42425), (31933/28275), (6526875134945677305855221241370040787/2441406250000000000000000000000000000), (8968281384945677305855221241370040787/2441406250000000000000000000000000000), 10, (14885410737918755071202194504612488539161/10000000000000000000000000000000000000000), (19482949014924368916400729113625138237451/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (47887/90312)

def qb : ℚ := (31933/60208)

def rho : ℚ := (3609577365715370937850694391/12500000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (280005681470478989361294137841/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell164Term01
