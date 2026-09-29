import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell141Term03
open CoupledFlow


def environment : Environment := ⟨(11953/10625), (31883/28325), (13540425803581623927967079205327228745411/5000000000000000000000000000000000000000), (18540425803581623927967079205327228745411/5000000000000000000000000000000000000000), 10, (7526093726397628798068366407268662592147/5000000000000000000000000000000000000000), (19636074803866360473537549372290992362807/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (11953/22578)

def qb : ℚ := (31883/60208)

def rho : ℚ := (285617802977937559740871647581/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (276897348452729488181885779591/1000000000000000000000000000000)

def finish : ℚ := (2289884975054009/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell141Term03
