import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell181Term00
open CoupledFlow


def environment : Environment := ⟨(95699/84925), (7977/7075), (6668202795814554762837871428339612833139/2500000000000000000000000000000000000000), (9168202795814554762837871428339612833139/2500000000000000000000000000000000000000), 10, (7427969477109474636224218881699701111337/5000000000000000000000000000000000000000), (19435225538722482950613260798263378041443/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (95699/180624)

def qb : ℚ := (7977/15052)

def rho : ℚ := (9031943191399526567038732629/31250000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (101051540006951311845677268873/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell181Term00
