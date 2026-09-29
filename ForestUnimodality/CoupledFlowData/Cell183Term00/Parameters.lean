import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell183Term00
open CoupledFlow


def environment : Environment := ⟨(95749/84875), (47887/42425), (6669874280758870415362010471078380431681/2500000000000000000000000000000000000000), (9169874280758870415362010471078380431681/2500000000000000000000000000000000000000), 10, (928697193420378411631979411487931209853/625000000000000000000000000000000000000), (3889784477657011494201794626880418139179/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (95749/180624)

def qb : ℚ := (47887/90312)

def rho : ℚ := (578240876100046068309384711/2000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (101130400797699006188743945419/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell183Term00
