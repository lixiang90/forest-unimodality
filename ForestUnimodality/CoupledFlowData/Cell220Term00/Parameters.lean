import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell220Term00
open CoupledFlow


def environment : Environment := ⟨(129/80), (33/20), (5977292904448473220787190779757513508347/2000000000000000000000000000000000000000), (7977292904448473220787190779757513508347/2000000000000000000000000000000000000000), 15, (15864834950957599998374424776529494054957/5000000000000000000000000000000000000000), (3104371059514146418466713393066013511503/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (129/209)

def qb : ℚ := (33/53)

def rho : ℚ := (78051729689748665840008951627/250000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (58643943207074338458157139587/1000000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell220Term00
