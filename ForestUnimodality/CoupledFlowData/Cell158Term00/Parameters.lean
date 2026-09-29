import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell158Term00
open CoupledFlow


def environment : Environment := ⟨(1549/1405), (2326/2105), (6642591335474354732247652242255351181827/2500000000000000000000000000000000000000), (9142591335474354732247652242255351181827/2500000000000000000000000000000000000000), 10, (3701664302543397324402657256051677167683/2500000000000000000000000000000000000000), (2399646518428497980953288096985550310193/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (1549/2954)

def qb : ℚ := (2326/4431)

def rho : ℚ := (287083780734784549866414279801/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (99594842628184207297425201969/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell158Term00
