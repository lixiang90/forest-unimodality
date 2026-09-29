import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell143Term00
open CoupledFlow


def environment : Environment := ⟨(22597/20875), (11311/10425), (5291982258909279004064762591211846074239/2000000000000000000000000000000000000000), (7291982258909279004064762591211846074239/2000000000000000000000000000000000000000), 9, (1789834743645155898111414106944362450911/1250000000000000000000000000000000000000), (18973042724172537452837810468622835605843/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (22597/43472)

def qb : ℚ := (11311/21736)

def rho : ℚ := (285453758047105653251015877733/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (70973423750888303823426300767/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell143Term00
