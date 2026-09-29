import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell051Term01
open CoupledFlow


def environment : Environment := ⟨(24/25), (9529/9875), (26404730679943674926230584200267064970751/10000000000000000000000000000000000000000), (36404730679943674926230584200267064970751/10000000000000000000000000000000000000000), 5, (13238770616692851983908317622853324234493/10000000000000000000000000000000000000000), (17877792138176833558650342034855950428071/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (24/49)

def qb : ℚ := (9529/19404)

def rho : ℚ := (134895741114062196576127227569/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (8567515610441353067794912241/50000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell051Term01
