import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell071Term00
open CoupledFlow


def environment : Environment := ⟨(4777/4925), (3193/3275), (25878934772184172017806174075597765952717/10000000000000000000000000000000000000000), (35878934772184172017806174075597765952717/10000000000000000000000000000000000000000), 5, (13011304578656253549566663165436639140279/10000000000000000000000000000000000000000), (276750538051716288972767648962642206553/156250000000000000000000000000000000000)⟩

def qa : ℚ := (4777/9702)

def qb : ℚ := (3193/6468)

def rho : ℚ := (137590790790889957990734724619/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (47167247155960521291074500297/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell071Term00
