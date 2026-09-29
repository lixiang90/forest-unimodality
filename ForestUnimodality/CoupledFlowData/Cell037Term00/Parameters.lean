import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell037Term00
open CoupledFlow


def environment : Environment := ⟨(1687/1885), (9/10), (3166140413281270408950824318305869147471/1250000000000000000000000000000000000000), (4416140413281270408950824318305869147471/1250000000000000000000000000000000000000), 3, (11816084960553835212085610630787133632863/10000000000000000000000000000000000000000), (8367423940953986038012088182053225753103/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (1687/3572)

def qb : ℚ := (9/19)

def rho : ℚ := (134077544585578531749777768827/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (90256775078790913444644797527/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell037Term00
