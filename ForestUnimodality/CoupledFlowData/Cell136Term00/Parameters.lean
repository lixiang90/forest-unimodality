import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell136Term00
open CoupledFlow


def environment : Environment := ⟨(11153/10375), (22331/20725), (3302233495960335809615381364889251627863/1250000000000000000000000000000000000000), (4552233495960335809615381364889251627863/1250000000000000000000000000000000000000), 9, (14299046108162703815638030861579226323471/10000000000000000000000000000000000000000), (2361016494757763353876836707063867477281/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (11153/21528)

def qb : ℚ := (22331/43056)

def rho : ℚ := (71208195180923970514870119999/250000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (12303204206562412702126801723/125000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell136Term00
