import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell098Term01
open CoupledFlow


def environment : Environment := ⟨1, (405/403), (26018351843367728847153903133758232128067/10000000000000000000000000000000000000000), (36018351843367728847153903133758232128067/10000000000000000000000000000000000000000), 6, (1645433283242301825946016846214306953549/1250000000000000000000000000000000000000), (18053753089806844286011547981648618826569/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (1/2)

def qb : ℚ := (405/808)

def rho : ℚ := (69580866157077100115074798619/250000000000000000000000000000)

def retention : ℚ := (1/2)

def rate : ℚ := (101164002005804175559434015097/500000000000000000000000000000)

def finish : ℚ := (13862943611198906188344642429163531361/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell098Term01
