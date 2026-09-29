import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell159Term02
open CoupledFlow


def environment : Environment := ⟨(31883/28325), (47837/42475), (26717299268613650417554599086182143778191/10000000000000000000000000000000000000000), (36717299268613650417554599086182143778191/10000000000000000000000000000000000000000), 10, (2975467750266429964390004235097083529407/2000000000000000000000000000000000000000), (19448638554263787702902818634131623836449/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (31883/60208)

def qb : ℚ := (47837/90312)

def rho : ℚ := (288521208286690535420192836193/1000000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (69982782539877448526786364171/250000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell159Term02
