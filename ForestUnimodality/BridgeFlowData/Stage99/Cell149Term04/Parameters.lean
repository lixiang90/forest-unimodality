import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell149Term04
open CoupledFlow


def environment : Environment := ⟨(113/100), (8069/7125), (27148272297877644939179872283563128158003/10000000000000000000000000000000000000000), (37148272297877644939179872283563128158003/10000000000000000000000000000000000000000), 10, (15084607627429232305941787324023864871349/10000000000000000000000000000000000000000), (9864071645767234336390759163356288044851/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (113/213)

def qb : ℚ := (8069/15194)

def rho : ℚ := (142958167685085240107766968883/500000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (139031470746677949797884226081/500000000000000000000000000000)

def finish : ℚ := (2295976662299297/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell149Term04
