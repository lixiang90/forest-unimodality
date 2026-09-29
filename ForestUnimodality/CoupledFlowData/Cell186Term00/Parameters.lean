import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell186Term00
open CoupledFlow


def environment : Environment := ⟨(113/100), (8069/7125), (13358936451221882921208582977778014892313/5000000000000000000000000000000000000000), (18358936451221882921208582977778014892313/5000000000000000000000000000000000000000), 10, (1487761467745802495952720910895908857929/1000000000000000000000000000000000000000), (19499573282204735196950382525693142314871/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (113/213)

def qb : ℚ := (8069/15194)

def rho : ℚ := (28926778816851058861545927453/100000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (6325241910714911448304525909/62500000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell186Term00
