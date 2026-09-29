import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell156Term00
open CoupledFlow


def environment : Environment := ⟨(11/10), (1549/1405), (13278330646917439491762195531557665501997/5000000000000000000000000000000000000000), (18278330646917439491762195531557665501997/5000000000000000000000000000000000000000), 10, (14800064543714575619026151024430114503101/10000000000000000000000000000000000000000), (3833870571709561783715591181906949744427/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (11/21)

def qb : ℚ := (1549/2954)

def rho : ℚ := (143441362524892641522403116519/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (12435971410822502200925775373/125000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell156Term00
