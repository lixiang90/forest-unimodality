import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell005Term01
open CoupledFlow


def environment : Environment := ⟨(2/5), (37/89), (13492063492063492063492063492063492063493/10000000000000000000000000000000000000000), (23492063492063492063492063492063492063493/10000000000000000000000000000000000000000), 0, (4789079550686828205859529039041955494579/10000000000000000000000000000000000000000), (3449231544469639707734945830183925422021/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (2/7)

def qb : ℚ := (37/126)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (22842055492324579001728439867/125000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell005Term01
