import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell024Term00
open CoupledFlow


def environment : Environment := ⟨(22/29), (67/86), (24663115679387860264747671359839698376603/10000000000000000000000000000000000000000), (34663115679387860264747671359839698376603/10000000000000000000000000000000000000000), 2, (11081459873384917533295503200009675722989/10000000000000000000000000000000000000000), (7589636439604531495876124121272090821021/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (22/51)

def qb : ℚ := (67/153)

def rho : ℚ := (126332699224849215948083175733/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (7280472308793186035419719867/62500000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell024Term00
