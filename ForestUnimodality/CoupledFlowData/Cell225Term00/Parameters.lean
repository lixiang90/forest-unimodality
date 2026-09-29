import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell225Term00
open CoupledFlow


def environment : Environment := ⟨(41/22), (83/43), (31095576594980129595875088020648115825637/10000000000000000000000000000000000000000), (41095576594980129595875088020648115825637/10000000000000000000000000000000000000000), 15, (32852041108911581158687073062262957874157/10000000000000000000000000000000000000000), (5414179138703731359456559215418720021473/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (41/63)

def qb : ℚ := (83/126)

def rho : ℚ := (160292229312734196300959058919/500000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (61630878006733697729171801531/1000000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell225Term00
