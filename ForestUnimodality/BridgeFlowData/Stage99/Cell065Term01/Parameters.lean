import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell065Term01
open CoupledFlow


def environment : Environment := ⟨(203/201), (407/401), (13102400259576155861244849169899265534251/5000000000000000000000000000000000000000), (18102400259576155861244849169899265534251/5000000000000000000000000000000000000000), 7, (6776355617240013012999252738178801622359/5000000000000000000000000000000000000000), (569900750746248099901504765791228424539/312500000000000000000000000000000000000)⟩

def qa : ℚ := (203/404)

def qb : ℚ := (407/808)

def rho : ℚ := (55651500802570641434412267059/200000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (270879507633886112257225320079/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell065Term01
