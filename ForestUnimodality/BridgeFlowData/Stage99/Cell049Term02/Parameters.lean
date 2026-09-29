import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell049Term02
open CoupledFlow


def environment : Environment := ⟨(4631/4875), (9287/9725), (413721188927054002390652414350011522313/156250000000000000000000000000000000000), (569971188927054002390652414350011522313/156250000000000000000000000000000000000), 4, (12866506650710183329140965877890084345679/10000000000000000000000000000000000000000), (4454721171105028840902157771570424580451/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (4631/9506)

def qb : ℚ := (9287/19012)

def rho : ℚ := (133910540371350580461765338571/500000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (135552388306006765294504888599/500000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell049Term02
