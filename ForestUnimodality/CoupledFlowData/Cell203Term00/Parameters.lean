import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell203Term00
open CoupledFlow


def environment : Environment := ⟨(97/80), (49/40), (5485934446077651623648983253587866445429/2000000000000000000000000000000000000000), (7485934446077651623648983253587866445429/2000000000000000000000000000000000000000), 13, (17014251264503509725468332125659231732117/10000000000000000000000000000000000000000), (20607347632460951098808998844146373922811/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (97/177)

def qb : ℚ := (49/89)

def rho : ℚ := (147092337427903255072197714871/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (10084332730090916375162267519/100000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell203Term00
