import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell131Term00
open CoupledFlow


def environment : Environment := ⟨(7339/6875), (107/100), (13187735154164969066711205004506588246511/5000000000000000000000000000000000000000), (18187735154164969066711205004506588246511/5000000000000000000000000000000000000000), 9, (7139624061356772947892616579189764546809/5000000000000000000000000000000000000000), (18802779338122238552058926912871545336973/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (7339/14214)

def qb : ℚ := (107/207)

def rho : ℚ := (142103513213412700830147483707/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (140517296976633734167467974629/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell131Term00
