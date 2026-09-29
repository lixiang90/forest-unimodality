import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell112Term00
open CoupledFlow


def environment : Environment := ⟨(5227/5075), (3493/3375), (1637480608353464466196424580665911991263/625000000000000000000000000000000000000), (2262480608353464466196424580665911991263/625000000000000000000000000000000000000), 8, (6836809401757016194034674417054887254407/5000000000000000000000000000000000000000), (18410820652250789470993852207958137648181/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (5227/10302)

def qb : ℚ := (3493/6868)

def rho : ℚ := (70247917686709070062629310199/250000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (139326929734016641652723819589/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell112Term00
