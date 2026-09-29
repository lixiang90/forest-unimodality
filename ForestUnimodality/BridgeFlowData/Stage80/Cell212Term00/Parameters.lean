import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell212Term00
open CoupledFlow


def environment : Environment := ⟨(53/40), (107/80), (14099978811539777976995115069125813814477/5000000000000000000000000000000000000000), (19099978811539777976995115069125813814477/5000000000000000000000000000000000000000), 14, (19824060162120057466617705890019993420271/10000000000000000000000000000000000000000), (109288648814692847248046915101415084393/50000000000000000000000000000000000000)⟩

def qa : ℚ := (53/93)

def qb : ℚ := (107/187)

def rho : ℚ := (74894391116193031996717472663/250000000000000000000000000000)

def retention : ℚ := (2/5)

def rate : ℚ := (18234547896796506572887614569/100000000000000000000000000000)

def finish : ℚ := (91629073187415506518352721176801107143/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell212Term00
