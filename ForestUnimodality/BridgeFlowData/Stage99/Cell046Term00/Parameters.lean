import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell046Term00
open CoupledFlow


def environment : Environment := ⟨(8999/9625), (47/50), (26591002216472826394199091490130481704681/10000000000000000000000000000000000000000), (36591002216472826394199091490130481704681/10000000000000000000000000000000000000000), 4, (2582764701638737959435814725279655373429/2000000000000000000000000000000000000000), (443241521694387330032824046401065113433/250000000000000000000000000000000000000)⟩

def qa : ℚ := (8999/18624)

def qb : ℚ := (47/97)

def rho : ℚ := (264838923846745320015319976931/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (92146041549243709068614374663/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell046Term00
