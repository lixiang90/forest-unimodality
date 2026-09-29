import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell204Term00
open CoupledFlow


def environment : Environment := ⟨(49/40), (99/80), (13756781352080677453957345250745672083283/5000000000000000000000000000000000000000), (18756781352080677453957345250745672083283/5000000000000000000000000000000000000000), 13, (8529667389495426730556708428491980634317/5000000000000000000000000000000000000000), (4149544924817848196517937832008539745799/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (49/89)

def qb : ℚ := (99/179)

def rho : ℚ := (29486542243932061334406846291/100000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (101622396095723485155817803377/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell204Term00
