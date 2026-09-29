import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell047Term01
open CoupledFlow


def environment : Environment := ⟨(23/25), (2983/3225), (25500893876449179696268210992597806578197/10000000000000000000000000000000000000000), (35500893876449179696268210992597806578197/10000000000000000000000000000000000000000), 4, (12456547465275797397591733554622370292137/10000000000000000000000000000000000000000), (8529249873827956107761603849139759747323/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (23/48)

def qb : ℚ := (2983/6208)

def rho : ℚ := (54140498241067669266592834031/200000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (130710109174550719546387363931/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell047Term01
