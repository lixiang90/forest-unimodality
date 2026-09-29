import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell109Term01
open CoupledFlow


def environment : Environment := ⟨(51/50), (10429/10175), (26139635324213443556214801406166917918919/10000000000000000000000000000000000000000), (36139635324213443556214801406166917918919/10000000000000000000000000000000000000000), 7, (13523662430754485819203938324108502066291/10000000000000000000000000000000000000000), (914628850699432156007969723997560636227/500000000000000000000000000000000000000)⟩

def qa : ℚ := (51/101)

def qb : ℚ := (10429/20604)

def rho : ℚ := (280115638765263004850299439077/1000000000000000000000000000000)

def retention : ℚ := (1/2)

def rate : ℚ := (1644219564496123224513034339/8000000000000000000000000000)

def finish : ℚ := (13862943611198906188344642429163531361/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell109Term01
