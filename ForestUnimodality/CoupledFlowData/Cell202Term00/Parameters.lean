import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell202Term00
open CoupledFlow


def environment : Environment := ⟨(6/5), (97/80), (6836161992261946026924746283167835338131/2500000000000000000000000000000000000000), (9336161992261946026924746283167835338131/2500000000000000000000000000000000000000), 13, (16968555544250116727678258091831080149153/10000000000000000000000000000000000000000), (2558213879235617979129097145387796688697/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (6/11)

def qb : ℚ := (97/177)

def rho : ℚ := (293494585528974264746505083037/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (100039438394037036923116479259/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell202Term00
