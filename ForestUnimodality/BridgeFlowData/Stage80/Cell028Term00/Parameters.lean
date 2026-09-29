import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell028Term00
open CoupledFlow


def environment : Environment := ⟨(17/20), (1613/1865), (25263855255980897679347618661120131228473/10000000000000000000000000000000000000000), (35263855255980897679347618661120131228473/10000000000000000000000000000000000000000), 3, (147374320596582840834068184699948194161/125000000000000000000000000000000000000), (8177199328334845882229400359457557744613/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (17/37)

def qb : ℚ := (1613/3478)

def rho : ℚ := (263029824478740944293464187019/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (25416223848724385596929000869/200000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell028Term00
