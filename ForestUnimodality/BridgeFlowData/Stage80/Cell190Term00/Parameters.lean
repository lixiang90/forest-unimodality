import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell190Term00
open CoupledFlow


def environment : Environment := ⟨(1291/1085), (2587/2165), (5444358166313851636871690157654869525443/2000000000000000000000000000000000000000), (7444358166313851636871690157654869525443/2000000000000000000000000000000000000000), 12, (984786745576748998553179641527743344113/625000000000000000000000000000000000000), (20263630656832843207688407447236055831567/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (1291/2376)

def qb : ℚ := (2587/4752)

def rho : ℚ := (292518089398658351476107780321/1000000000000000000000000000000)

def retention : ℚ := (19/20)

def rate : ℚ := (3364333319407598038640284889/125000000000000000000000000000)

def finish : ℚ := (5129329438755053342619614425468723841/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell190Term00
