import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell082Term01
open CoupledFlow


def environment : Environment := ⟨(197/199), (395/397), (26005396953400579965781842458543699710981/10000000000000000000000000000000000000000), (36005396953400579965781842458543699710981/10000000000000000000000000000000000000000), 5, (6533011530296416840666374734239204994367/5000000000000000000000000000000000000000), (17957237116910642785964429003945405790199/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (197/396)

def qb : ℚ := (395/792)

def rho : ℚ := (277034786969773868888860947183/1000000000000000000000000000000)

def retention : ℚ := (9/20)

def rate : ℚ := (110125100090672257492523308593/500000000000000000000000000000)

def finish : ℚ := (1996269240544429/2500000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell082Term01
