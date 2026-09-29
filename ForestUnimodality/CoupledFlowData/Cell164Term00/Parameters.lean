import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell164Term00
open CoupledFlow


def environment : Environment := ⟨(23557/21175), (11791/10575), (26624589585769659439703627395080264895741/10000000000000000000000000000000000000000), (36624589585769659439703627395080264895741/10000000000000000000000000000000000000000), 10, (14832742383724129176923246867942331485869/10000000000000000000000000000000000000000), (193079019854158121458260516236873559593/100000000000000000000000000000000000000)⟩

def qa : ℚ := (23557/44732)

def qb : ℚ := (11791/22366)

def rho : ℚ := (143942669314310070142394095669/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (20039346364942857034551143617/200000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell164Term00
