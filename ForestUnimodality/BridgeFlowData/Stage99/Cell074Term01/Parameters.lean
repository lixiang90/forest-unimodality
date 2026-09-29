import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell074Term01
open CoupledFlow


def environment : Environment := ⟨(3493/3375), (26/25), (26421637636177076283453031321469705937943/10000000000000000000000000000000000000000), (36421637636177076283453031321469705937943/10000000000000000000000000000000000000000), 8, (1721680591743059508507791677918809822061/1250000000000000000000000000000000000000), (9283946848437293954605674650570709356731/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (3493/6868)

def qb : ℚ := (26/51)

def rho : ℚ := (139972816890102361447934607439/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (11057908850414324207505557551/62500000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell074Term01
