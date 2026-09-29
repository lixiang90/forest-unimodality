import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell184Term01
open CoupledFlow


def environment : Environment := ⟨2, (35/17), (8000035945378137186659121003923505325499/2500000000000000000000000000000000000000), (10500035945378137186659121003923505325499/2500000000000000000000000000000000000000), 15, (33691229867794276918956690588715406516949/10000000000000000000000000000000000000000), (1130773101809953235486366877345608265823/400000000000000000000000000000000000000)⟩

def qa : ℚ := (2/3)

def qb : ℚ := (35/52)

def rho : ℚ := (320511723282811865010425490097/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (143893204145686426703481255277/1000000000000000000000000000000)

def finish : ℚ := (4469724207952419/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell184Term01
