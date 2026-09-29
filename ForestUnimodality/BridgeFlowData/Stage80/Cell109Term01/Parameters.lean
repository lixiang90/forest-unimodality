import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell109Term01
open CoupledFlow


def environment : Environment := ⟨(22331/20725), (27/25), (26482261090698136313884087957974200867581/10000000000000000000000000000000000000000), (36482261090698136313884087957974200867581/10000000000000000000000000000000000000000), 9, (716455687755520360032719382615914754797/500000000000000000000000000000000000000), (2367839061175119424218438401118517844771/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (22331/43056)

def qb : ℚ := (27/52)

def rho : ℚ := (284648348927669528564054813597/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (269247009452612244353134560879/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell109Term01
