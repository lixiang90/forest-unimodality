import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell198Term00
open CoupledFlow


def environment : Environment := ⟨(643/545), (859/725), (27097949444476505043588302435316122121201/10000000000000000000000000000000000000000), (37097949444476505043588302435316122121201/10000000000000000000000000000000000000000), 12, (122613530030994887931729146746001145107/78125000000000000000000000000000000000), (5029535759596798900322340876252611884803/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (643/1188)

def qb : ℚ := (859/1584)

def rho : ℚ := (1142031576034323842323856717/3906250000000000000000000000)

def retention : ℚ := (19/20)

def rate : ℚ := (5355023584921567447152264203/200000000000000000000000000000)

def finish : ℚ := (5129329438755053342619614425468723841/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell198Term00
