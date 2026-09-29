import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell002Term00
open CoupledFlow


def environment : Environment := ⟨(37/103), (19/51), (2342857142857142857142857142857142857143/2000000000000000000000000000000000000000), (4342857142857142857142857142857142857143/2000000000000000000000000000000000000000), 0, (4290253557988937172495834642957456682309/10000000000000000000000000000000000000000), (5893877551020408163265306122448979591837/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (37/140)

def qb : ℚ := (19/70)

def rho : ℚ := (1/4)

def retention : ℚ := (1/20)

def rate : ℚ := (172451879257813692026267963281/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell002Term00
