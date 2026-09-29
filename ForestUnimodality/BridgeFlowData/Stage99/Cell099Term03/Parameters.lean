import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03
open CoupledFlow


def environment : Environment := ⟨(22331/20725), (27/25), (2673361093636954618202554898616302488161/1000000000000000000000000000000000000000), (3673361093636954618202554898616302488161/1000000000000000000000000000000000000000), 9, (2889292722198702817166583405945916433779/2000000000000000000000000000000000000000), (4768305265778739167859085685703854191363/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (22331/43056)

def qb : ℚ := (27/52)

def rho : ℚ := (282700641725741439986015727903/1000000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (67989372566735713913086127531/250000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03
