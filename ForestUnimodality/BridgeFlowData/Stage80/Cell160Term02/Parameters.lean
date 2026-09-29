import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell160Term02
open CoupledFlow


def environment : Environment := ⟨(47837/42475), (95699/84925), (26720656688395798560256847723884877528727/10000000000000000000000000000000000000000), (36720656688395798560256847723884877528727/10000000000000000000000000000000000000000), 10, (14878953716748868491570768398430374211759/10000000000000000000000000000000000000000), (1945549940441353046338260735189154760509/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (47837/90312)

def qb : ℚ := (95699/180624)

def rho : ℚ := (144285106627308672601029574567/500000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (280331788821704500823524824301/1000000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell160Term02
