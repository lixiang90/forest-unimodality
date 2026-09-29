import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell135Term00
open CoupledFlow


def environment : Environment := ⟨(7427/6925), (11153/10375), (26403659067425228678987085336273573844893/10000000000000000000000000000000000000000), (36403659067425228678987085336273573844893/10000000000000000000000000000000000000000), 9, (2858482241230569731237679505886886559673/2000000000000000000000000000000000000000), (471490627994929365775667691791456671651/250000000000000000000000000000000000000)⟩

def qa : ℚ := (7427/14352)

def qb : ℚ := (11153/21528)

def rho : ℚ := (284624954835464599161975806289/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (28201192091551525695885303629/200000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell135Term00
