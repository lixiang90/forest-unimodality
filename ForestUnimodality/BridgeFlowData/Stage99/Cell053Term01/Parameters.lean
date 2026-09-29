import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell053Term01
open CoupledFlow


def environment : Environment := ⟨(4777/4925), (3193/3275), (26333927606496756212420482139304624497693/10000000000000000000000000000000000000000), (36333927606496756212420482139304624497693/10000000000000000000000000000000000000000), 5, (6604073092506692871333517274012040953503/5000000000000000000000000000000000000000), (17936646698754505656502566399319676255587/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (4777/9702)

def qb : ℚ := (3193/6468)

def rho : ℚ := (271735610942147606353944538587/1000000000000000000000000000000)

def retention : ℚ := (1/2)

def rate : ℚ := (50881261337729073755840934949/250000000000000000000000000000)

def finish : ℚ := (13862943611198906188344642429163531361/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell053Term01
