import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell037Term00
open CoupledFlow


def environment : Environment := ⟨(1733/1915), (869/955), (13407116248412456200282143852525919889713/5000000000000000000000000000000000000000), (18407116248412456200282143852525919889713/5000000000000000000000000000000000000000), 4, (520296486484534385451572719375916100771/400000000000000000000000000000000000000), (274050575998328269566289456685941344301/156250000000000000000000000000000000000)⟩

def qa : ℚ := (1733/3648)

def qb : ℚ := (869/1824)

def rho : ℚ := (129413383434676007700179902077/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (64532905908790994423315790283/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell037Term00
