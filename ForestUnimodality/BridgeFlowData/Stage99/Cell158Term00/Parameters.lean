import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell158Term00
open CoupledFlow


def environment : Environment := ⟨(643/545), (6/5), (5554952560778986962633175297814507003731/2000000000000000000000000000000000000000), (7554952560778986962633175297814507003731/2000000000000000000000000000000000000000), 12, (16033607624472951310230399399994365902517/10000000000000000000000000000000000000000), (10302208037425891312681602678837964095997/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (643/1188)

def qb : ℚ := (6/11)

def rho : ℚ := (288793101513957852993327848939/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (142151876488996030101488162579/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell158Term00
