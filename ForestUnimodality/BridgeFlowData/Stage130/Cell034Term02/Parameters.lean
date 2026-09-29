import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell034Term02
open CoupledFlow


def environment : Environment := ⟨(9/10), (1733/1915), (5600877192982456140350877192982456140351/2000000000000000000000000000000000000000), (7600877192982456140350877192982456140351/2000000000000000000000000000000000000000), 4, (1350610831915212947552031922669496044499/1000000000000000000000000000000000000000), (18054166907125269313634964604493690366267/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (9/19)

def qb : ℚ := (1733/3648)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (9657679567638546514340572827/40000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell034Term02
