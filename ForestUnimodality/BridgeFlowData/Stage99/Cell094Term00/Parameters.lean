import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell094Term00
open CoupledFlow


def environment : Environment := ⟨(7427/6925), (11153/10375), (26692555959187536982886238974035325497991/10000000000000000000000000000000000000000), (36692555959187536982886238974035325497991/10000000000000000000000000000000000000000), 9, (14427297554141675137582841946547181584457/10000000000000000000000000000000000000000), (1900929378543378855305324337037420964693/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (7427/14352)

def qb : ℚ := (11153/21528)

def rho : ℚ := (282383975361006264950265560771/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (28200866188302976293094048059/200000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell094Term00
