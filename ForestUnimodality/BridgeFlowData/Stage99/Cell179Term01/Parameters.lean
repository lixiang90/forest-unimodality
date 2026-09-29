import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell179Term01
open CoupledFlow


def environment : Environment := ⟨(467/275), (236/135), (1234112845560906570820883986690417938407/400000000000000000000000000000000000000), (1634112845560906570820883986690417938407/400000000000000000000000000000000000000), 15, (32626762261747517074725288698507988102009/10000000000000000000000000000000000000000), (12993619661468125024047460271527581990029/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (467/742)

def qb : ℚ := (236/371)

def rho : ℚ := (311419667306710463585673929619/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (55688998339895937141144231193/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell179Term01
