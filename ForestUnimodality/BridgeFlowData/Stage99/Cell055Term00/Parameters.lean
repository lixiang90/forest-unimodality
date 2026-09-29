import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell055Term00
open CoupledFlow


def environment : Environment := ⟨(3193/3275), (49/50), (26298222445187699155373711030159868514313/10000000000000000000000000000000000000000), (36298222445187699155373711030159868514313/10000000000000000000000000000000000000000), 5, (2638540391498036223118685265405656561543/2000000000000000000000000000000000000000), (3593157373362014663865276445409764762023/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (3193/6468)

def qb : ℚ := (49/99)

def rho : ℚ := (68178200144221353120664564907/250000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (11829619407256503363163820807/125000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell055Term00
