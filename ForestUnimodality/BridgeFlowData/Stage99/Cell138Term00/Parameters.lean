import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell138Term00
open CoupledFlow


def environment : Environment := ⟨(95549/85075), (15929/14175), (5413262939352616449446137107863799871353/2000000000000000000000000000000000000000), (7413262939352616449446137107863799871353/2000000000000000000000000000000000000000), 10, (15045196955791566249741946541169224361583/10000000000000000000000000000000000000000), (9806492937894285429114695554674002470667/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (95549/180624)

def qb : ℚ := (15929/30104)

def rho : ℚ := (57101154570764159623006738693/200000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50404860343244208505617677589/500000000000000000000000000000)

def finish : ℚ := (2231435513142097/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell138Term00
