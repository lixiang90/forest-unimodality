import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell201Term00
open CoupledFlow


def environment : Environment := ⟨(2587/2165), (6/5), (3400693990691189826702511043800786821709/1250000000000000000000000000000000000000), (4650693990691189826702511043800786821709/1250000000000000000000000000000000000000), 12, (15748451059460588425673388053582668076979/10000000000000000000000000000000000000000), (507348435348129799276637568414631289641/250000000000000000000000000000000000000)⟩

def qa : ℚ := (2587/4752)

def qb : ℚ := (6/11)

def rho : ℚ := (293211371542787514015681664661/1000000000000000000000000000000)

def retention : ℚ := (19/20)

def rate : ℚ := (26966784789376477831236396619/1000000000000000000000000000000)

def finish : ℚ := (5129329438755053342619614425468723841/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell201Term00
