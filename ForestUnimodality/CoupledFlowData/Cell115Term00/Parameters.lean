import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell115Term00
open CoupledFlow


def environment : Environment := ⟨(3493/3375), (26/25), (26229654298277246454055399975949720210669/10000000000000000000000000000000000000000), (36229654298277246454055399975949720210669/10000000000000000000000000000000000000000), 8, (13687097106875650669531107277560721520903/10000000000000000000000000000000000000000), (4617504959584354940222747055758297673909/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (3493/6868)

def qb : ℚ := (26/51)

def rho : ℚ := (28142908423659405362883567679/100000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (139810597704783401184319942191/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell115Term00
