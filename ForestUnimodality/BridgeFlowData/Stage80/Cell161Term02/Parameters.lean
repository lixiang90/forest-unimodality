import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell161Term02
open CoupledFlow


def environment : Environment := ⟨(95699/84925), (7977/7075), (26724013479553090739242005284335835805787/10000000000000000000000000000000000000000), (36724013479553090739242005284335835805787/10000000000000000000000000000000000000000), 10, (2976113675086868628456606742988330470603/2000000000000000000000000000000000000000), (9731180425405095828691651479974321094299/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (95699/180624)

def qb : ℚ := (7977/15052)

def rho : ℚ := (144309607101316342660581204521/500000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (140202328025513499883132353723/500000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell161Term02
