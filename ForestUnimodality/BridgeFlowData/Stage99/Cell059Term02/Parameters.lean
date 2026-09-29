import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell059Term02
open CoupledFlow


def environment : Environment := ⟨(395/397), 1, (13076857952133303078176048529650873163759/5000000000000000000000000000000000000000), (18076857952133303078176048529650873163759/5000000000000000000000000000000000000000), 5, (6565095542640279009775122812672388901849/5000000000000000000000000000000000000000), (18076857952133303078176048529650873163759/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (395/792)

def qb : ℚ := (1/2)

def rho : ℚ := (276596741161532185446345206469/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (280051586027378547469963779969/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell059Term02
