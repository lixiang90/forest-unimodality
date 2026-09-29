import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell200Term01
open CoupledFlow


def environment : Environment := ⟨(1291/1085), (2587/2165), (13584859521115424333556031314371738557001/5000000000000000000000000000000000000000), (18584859521115424333556031314371738557001/5000000000000000000000000000000000000000), 12, (15730495827160648314713637928847479608681/10000000000000000000000000000000000000000), (10117641325994445023339531357382089151297/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (1291/2376)

def qb : ℚ := (2587/4752)

def rho : ℚ := (14646394186725685118534796967/50000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (20242604561185996546710584383/200000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell200Term01
