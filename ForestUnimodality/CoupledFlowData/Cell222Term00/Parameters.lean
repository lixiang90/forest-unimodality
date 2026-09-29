import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell222Term00
open CoupledFlow


def environment : Environment := ⟨(467/275), (236/135), (15177195160354950781809152114895538549793/5000000000000000000000000000000000000000), (20177195160354950781809152114895538549793/5000000000000000000000000000000000000000), 15, (8041029814264821097706911903767401014329/2500000000000000000000000000000000000000), (25670178209400368649633207003317235028309/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (467/742)

def qb : ℚ := (236/371)

def rho : ℚ := (39408264709694598766694616437/125000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (29988258768335105035531109167/500000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell222Term00
