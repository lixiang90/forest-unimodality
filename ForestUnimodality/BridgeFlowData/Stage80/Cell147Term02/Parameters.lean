import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell147Term02
open CoupledFlow


def environment : Environment := ⟨(94453/84475), (47239/42225), (3334620231120775081248244384199564690341/1250000000000000000000000000000000000000), (4584620231120775081248244384199564690341/1250000000000000000000000000000000000000), 10, (2971587110556791855305309587170631526177/2000000000000000000000000000000000000000), (4841564765669191944538268274729572485179/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (94453/178928)

def qb : ℚ := (47239/89464)

def rho : ℚ := (287931397893111994638305749963/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (2778748926653323768001839/10000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell147Term02
