import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell002Term02
open CoupledFlow


def environment : Environment := ⟨(37/103), (19/51), (2342857142857142857142857142857142857143/2000000000000000000000000000000000000000), (4342857142857142857142857142857142857143/2000000000000000000000000000000000000000), 0, (4290253557988937172495834642957456682309/10000000000000000000000000000000000000000), (5893877551020408163265306122448979591837/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (37/140)

def qb : ℚ := (19/70)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (173541632468508699041012547353/1000000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell002Term02
