import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell182Term00
open CoupledFlow


def environment : Environment := ⟨(7977/7075), (95749/84875), (2667615446602435238515230475718182413969/1000000000000000000000000000000000000000), (3667615446602435238515230475718182413969/1000000000000000000000000000000000000000), 10, (14857547177144345675610533911424322599567/10000000000000000000000000000000000000000), (4860518416665788760804140131150072082823/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (7977/15052)

def qb : ℚ := (95749/180624)

def rho : ℚ := (144535656049660629928642601763/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (25269478167954000930997157823/250000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell182Term00
