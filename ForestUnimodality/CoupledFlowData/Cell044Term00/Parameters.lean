import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell044Term00
open CoupledFlow


def environment : Environment := ⟨(869/955), (581/635), (6358255406607678128406476771852134894901/2500000000000000000000000000000000000000), (8858255406607678128406476771852134894901/2500000000000000000000000000000000000000), 4, (12428062140001367348886387133744630750383/10000000000000000000000000000000000000000), (1692975786591796379146106251462529728269/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (869/1824)

def qb : ℚ := (581/1216)

def rho : ℚ := (269689702260771572442712612683/1000000000000000000000000000000)

def retention : ℚ := (1/2)

def rate : ℚ := (38660805938271872885316216733/200000000000000000000000000000)

def finish : ℚ := (13862943611198906188344642429163531361/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell044Term00
