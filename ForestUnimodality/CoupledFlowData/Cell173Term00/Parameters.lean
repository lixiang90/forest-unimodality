import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell173Term00
open CoupledFlow


def environment : Environment := ⟨(31833/28375), (23881/21275), (13323022370845062194591654744479650127827/5000000000000000000000000000000000000000), (18323022370845062194591654744479650127827/5000000000000000000000000000000000000000), 10, (593722532293740890811035739758487459469/400000000000000000000000000000000000000), (19380463160516916036364749178533019962027/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (31833/60208)

def qb : ℚ := (23881/45156)

def rho : ℚ := (288628978545076860109350895663/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (25180925628998892555349671597/250000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell173Term00
