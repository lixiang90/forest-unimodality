import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell157Term00
open CoupledFlow


def environment : Environment := ⟨(29/25), (643/545), (13814941159629611220433055895956450407369/5000000000000000000000000000000000000000), (18814941159629611220433055895956450407369/5000000000000000000000000000000000000000), 12, (7980519276209993167682839811548624474453/5000000000000000000000000000000000000000), (10183507715186734019140113586784509774359/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (29/54)

def qb : ℚ := (643/1188)

def rho : ℚ := (287668075416105180383471406319/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (139664773560094695307690027377/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell157Term00
