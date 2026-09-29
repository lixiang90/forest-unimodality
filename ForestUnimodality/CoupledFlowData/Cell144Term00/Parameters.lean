import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell144Term00
open CoupledFlow


def environment : Environment := ⟨(11311/10425), (22647/20825), (26473945957360876446269328426289499515187/10000000000000000000000000000000000000000), (36473945957360876446269328426289499515187/10000000000000000000000000000000000000000), 9, (89532694915634814685819764844071342151/62500000000000000000000000000000000000), (19001321634531463214912161411257321851317/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (11311/21736)

def qb : ℚ := (22647/43472)

def rho : ℚ := (142829629203145994405459741547/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (99002451318928540374764834427/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell144Term00
