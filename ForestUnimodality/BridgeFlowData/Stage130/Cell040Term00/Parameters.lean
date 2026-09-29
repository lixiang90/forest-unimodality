import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell040Term00
open CoupledFlow


def environment : Environment := ⟨(23/25), (2983/3225), (28440721649484536082474226804123711340207/10000000000000000000000000000000000000000), (38440721649484536082474226804123711340207/10000000000000000000000000000000000000000), 4, (6844416308883970673936671566247473939277/5000000000000000000000000000000000000000), (18471113511664363906897651185035604208737/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (23/48)

def qb : ℚ := (2983/6208)

def rho : ℚ := (1/4)

def retention : ℚ := (7/10)

def rate : ℚ := (122912103902802830498104727073/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell040Term00
