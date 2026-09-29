import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell119Term02
open CoupledFlow


def environment : Environment := ⟨(1549/1405), (2326/2105), (26934135986712230205170897364903443824447/10000000000000000000000000000000000000000), (36934135986712230205170897364903443824447/10000000000000000000000000000000000000000), 10, (3745407833473985411280383447965472434557/2500000000000000000000000000000000000000), (1938812915935288816457402556325105175709/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (1549/2954)

def qb : ℚ := (2326/4431)

def rho : ℚ := (142128121651219543328701808967/500000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (275076956599494715540601584323/1000000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell119Term02
