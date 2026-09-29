import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell117Term02
open CoupledFlow


def environment : Environment := ⟨(11/10), (1549/1405), (26914303492938046458140812468056319381553/10000000000000000000000000000000000000000), (36914303492938046458140812468056319381553/10000000000000000000000000000000000000000), 10, (59888372748439917099039295394440035693/40000000000000000000000000000000000000), (967844551634411543054504375643521305383/500000000000000000000000000000000000000)⟩

def qa : ℚ := (11/21)

def qb : ℚ := (1549/2954)

def rho : ℚ := (14205163877335087278092790619/50000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (137287215900089548347089943393/500000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell117Term02
