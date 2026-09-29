import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell157Term01
open CoupledFlow


def environment : Environment := ⟨(95599/85025), (11953/10625), (6677645693822327904553095164420252814649/2500000000000000000000000000000000000000), (9177645693822327904553095164420252814649/2500000000000000000000000000000000000000), 10, (2974821602388114383018265169335852488883/2000000000000000000000000000000000000000), (4858729691658175455891715231655384971809/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (95599/180624)

def qb : ℚ := (11953/22578)

def rho : ℚ := (72105796113242923141953222973/250000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (34861572760523811104156496519/125000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell157Term01
