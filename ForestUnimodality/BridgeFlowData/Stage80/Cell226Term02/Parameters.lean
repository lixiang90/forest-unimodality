import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell226Term02
open CoupledFlow


def environment : Environment := ⟨(236/135), (9/5), (15311060600053775981893007665444019582717/5000000000000000000000000000000000000000), (20311060600053775981893007665444019582717/5000000000000000000000000000000000000000), 15, (32412642991418522738240702174659955630823/10000000000000000000000000000000000000000), (5222844154299542395343916256828462178413/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (236/371)

def qb : ℚ := (9/14)

def rho : ℚ := (158252972485208580231965163719/500000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (27275834829327214906510698951/125000000000000000000000000000)

def finish : ℚ := (2987963976195263/1600000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell226Term02
