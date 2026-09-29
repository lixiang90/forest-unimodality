import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell150Term01
open CoupledFlow


def environment : Environment := ⟨(28/25), (95449/85175), (5337411458283575170997329161364257872343/2000000000000000000000000000000000000000), (7337411458283575170997329161364257872343/2000000000000000000000000000000000000000), 10, (371569793622719201777894111504318405071/250000000000000000000000000000000000000), (1211682463089257529620447848713101957757/625000000000000000000000000000000000000)⟩

def qa : ℚ := (28/53)

def qb : ℚ := (95449/180624)

def rho : ℚ := (57615991565161220026082559019/200000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (278094565968251973842597612537/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell150Term01
