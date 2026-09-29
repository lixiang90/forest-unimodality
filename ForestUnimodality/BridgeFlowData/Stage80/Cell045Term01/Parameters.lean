import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell045Term01
open CoupledFlow


def environment : Environment := ⟨(8999/9625), (47/50), (3206277484574276207752963932779781942453/1250000000000000000000000000000000000000), (4456277484574276207752963932779781942453/1250000000000000000000000000000000000000), 4, (500768479787887760809726632404335382913/400000000000000000000000000000000000000), (4318454469587442922977099068879376315367/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (8999/18624)

def qb : ℚ := (47/97)

def rho : ℚ := (271827822746385951737277174623/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (268970266092928387459954756949/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell045Term01
