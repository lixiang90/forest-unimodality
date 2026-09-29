import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell092Term00
open CoupledFlow


def environment : Environment := ⟨(107/100), (7427/6925), (2667201123501763090765919361083902280437/1000000000000000000000000000000000000000), (3667201123501763090765919361083902280437/1000000000000000000000000000000000000000), 9, (1802213280214056677337485695720113560703/1250000000000000000000000000000000000000), (4744339246141233708737193961602937262543/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (107/207)

def qb : ℚ := (7427/14352)

def rho : ℚ := (70556377234341421603026823959/250000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (70357952374318325070880850253/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell092Term00
