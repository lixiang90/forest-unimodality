import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell114Term01
open CoupledFlow


def environment : Environment := ⟨(1531/1395), (11/10), (2689465068756358671244924629484193386967/1000000000000000000000000000000000000000), (3689465068756358671244924629484193386967/1000000000000000000000000000000000000000), 9, (3630409286679614906607439293594860748907/2500000000000000000000000000000000000000), (19325769407771402563663890916345774884113/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (1531/2926)

def qb : ℚ := (11/21)

def rho : ℚ := (283948764413204767844791896711/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (5506396843505840783651182327/20000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell114Term01
