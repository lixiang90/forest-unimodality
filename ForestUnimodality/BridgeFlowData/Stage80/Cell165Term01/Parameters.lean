import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell165Term01
open CoupledFlow


def environment : Environment := ⟨(31933/28275), (113/100), (1336871753357427898212885986685977361721/500000000000000000000000000000000000000), (1836871753357427898212885986685977361721/500000000000000000000000000000000000000), 10, (14887024284078127766321029380028619612433/10000000000000000000000000000000000000000), (2436226621236964231197841742905110820123/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (31933/60208)

def qb : ℚ := (113/213)

def rho : ℚ := (144407586146176648485794652351/500000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (70019595220832423891268442627/250000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell165Term01
