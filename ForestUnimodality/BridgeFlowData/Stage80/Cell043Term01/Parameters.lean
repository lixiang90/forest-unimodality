import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell043Term01
open CoupledFlow


def environment : Environment := ⟨(2983/3225), (4487/4825), (5116347542659786596982349858865434078481/2000000000000000000000000000000000000000), (7116347542659786596982349858865434078481/2000000000000000000000000000000000000000), 4, (12490474556617794772892974981600387073563/10000000000000000000000000000000000000000), (4286277306689548762438225383474173473763/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (2983/6208)

def qb : ℚ := (4487/9312)

def rho : ℚ := (270841957440629035562772258939/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (53260130197868557049883485929/200000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell043Term01
