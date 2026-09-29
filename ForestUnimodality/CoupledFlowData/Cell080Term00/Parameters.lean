import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell080Term00
open CoupledFlow


def environment : Environment := ⟨(49/50), (131/133), (25893949109208399847477960914862507815453/10000000000000000000000000000000000000000), (35893949109208399847477960914862507815453/10000000000000000000000000000000000000000), 5, (3254450348546522031285875199359158627963/2500000000000000000000000000000000000000), (8905506313080114356097751666376872204213/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (49/99)

def qb : ℚ := (131/264)

def rho : ℚ := (276487894771556723313577579743/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (23728479137628599089374530441/250000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell080Term00
