import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell097Term02
open CoupledFlow


def environment : Environment := ⟨(11153/10375), (22331/20725), (5342617837309025013107255007775174137967/2000000000000000000000000000000000000000), (7342617837309025013107255007775174137967/2000000000000000000000000000000000000000), 9, (7218441670354065490032403871528054970419/5000000000000000000000000000000000000000), (2380156060202814903377260306034980805157/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (11153/21528)

def qb : ℚ := (22331/43056)

def rho : ℚ := (35317794113417466279116568101/125000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (135838405981017846050988215793/500000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell097Term02
