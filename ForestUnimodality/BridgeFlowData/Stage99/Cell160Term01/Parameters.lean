import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell160Term01
open CoupledFlow


def environment : Environment := ⟨(97/80), (49/40), (13945989429749306278287213691500287693051/5000000000000000000000000000000000000000), (18945989429749306278287213691500287693051/5000000000000000000000000000000000000000), 13, (8631332206852050811607165640070929142183/5000000000000000000000000000000000000000), (5215469000324247233910525117323112904267/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (97/177)

def qb : ℚ := (49/89)

def rho : ℚ := (5811908634217938902258521987/20000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (225347803716007615239085670147/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell160Term01
