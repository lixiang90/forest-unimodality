import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell227Term00
open CoupledFlow


def environment : Environment := ⟨2, (35/17), (31487714885524343642293191633037268771589/10000000000000000000000000000000000000000), (41487714885524343642293191633037268771589/10000000000000000000000000000000000000000), 15, (33215885975376133657409807647768871256151/10000000000000000000000000000000000000000), (27924423480641385143851186676082777057801/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2/3)

def qb : ℚ := (35/52)

def rho : ℚ := (32447047273349308038110966633/100000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (3108984815985449218926151757/50000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell227Term00
