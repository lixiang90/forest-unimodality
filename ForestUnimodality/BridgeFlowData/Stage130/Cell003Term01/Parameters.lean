import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell003Term01
open CoupledFlow


def environment : Environment := ⟨(19/51), (39/101), (6142857142857142857142857142857142857143/5000000000000000000000000000000000000000), (11142857142857142857142857142857142857143/5000000000000000000000000000000000000000), 0, (2225541869353371199160037520056189111471/5000000000000000000000000000000000000000), (388010204081632653061224489795918367347/625000000000000000000000000000000000000)⟩

def qa : ℚ := (19/70)

def qb : ℚ := (39/140)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (176812846031925986888573827373/1000000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell003Term01
