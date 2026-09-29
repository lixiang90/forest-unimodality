import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell174Term00
open CoupledFlow


def environment : Environment := ⟨(23881/21275), (95549/85075), (26649392588477674150991047648704430051667/10000000000000000000000000000000000000000), (36649392588477674150991047648704430051667/10000000000000000000000000000000000000000), 10, (593786950420999380830337705048029535003/400000000000000000000000000000000000000), (2423413287019203765455479069632260654043/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (23881/45156)

def qb : ℚ := (95549/180624)

def rho : ℚ := (288678144320814378008842598291/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (100783983257196478189321729067/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell174Term00
