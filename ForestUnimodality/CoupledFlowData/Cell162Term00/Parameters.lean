import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell162Term00
open CoupledFlow


def environment : Environment := ⟨(4657/4205), (111/100), (26597745421001488326131127603708881328459/10000000000000000000000000000000000000000), (36597745421001488326131127603708881328459/10000000000000000000000000000000000000000), 10, (926239302775718823737239689585647465659/625000000000000000000000000000000000000), (19252842377872820872988413099581449419237/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (4657/8862)

def qb : ℚ := (111/211)

def rho : ℚ := (287485660474057036756613427693/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (99947243167094260935260988339/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell162Term00
