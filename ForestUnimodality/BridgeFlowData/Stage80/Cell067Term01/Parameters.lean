import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell067Term01
open CoupledFlow


def environment : Environment := ⟨(24/25), (9529/9875), (12906924837481243309656416746303876718133/5000000000000000000000000000000000000000), (17906924837481243309656416746303876718133/5000000000000000000000000000000000000000), 5, (1622892598361001681850146660760602800087/1250000000000000000000000000000000000000), (17587619746068724747239331599209404375087/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (24/49)

def qb : ℚ := (9529/19404)

def rho : ℚ := (5484853674987100698664872197/20000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (134896922389747715414178815209/500000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell067Term01
