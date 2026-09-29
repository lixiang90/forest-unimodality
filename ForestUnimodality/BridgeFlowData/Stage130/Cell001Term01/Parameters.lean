import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell001Term01
open CoupledFlow


def environment : Environment := ⟨(9/26), (37/103), (11142857142857142857142857142857142857143/10000000000000000000000000000000000000000), (21142857142857142857142857142857142857143/10000000000000000000000000000000000000000), 0, (4128881313135457963023680513259102734973/10000000000000000000000000000000000000000), (2793877551020408163265306122448979591837/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (9/35)

def qb : ℚ := (37/140)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (170276270206149628120850098983/1000000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell001Term01
