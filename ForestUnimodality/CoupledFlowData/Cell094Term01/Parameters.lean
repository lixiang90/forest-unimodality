import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell094Term01
open CoupledFlow


def environment : Environment := ⟨(395/397), 1, (12994332864019000418432721766761790060151/5000000000000000000000000000000000000000), (17994332864019000418432721766761790060151/5000000000000000000000000000000000000000), 5, (13058784028451031401993498796366983284583/10000000000000000000000000000000000000000), (17994332864019000418432721766761790060151/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (395/792)

def qb : ℚ := (1/2)

def rho : ℚ := (277865261123287868271521379491/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (138406247615570965975566115673/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell094Term01
