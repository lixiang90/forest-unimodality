import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell195Term00
open CoupledFlow


def environment : Environment := ⟨(2557/2195), (427/365), (1686877122396164389746054663655053602153/625000000000000000000000000000000000000), (2311877122396164389746054663655053602153/625000000000000000000000000000000000000), 12, (15640451267704930917928911527043187944109/10000000000000000000000000000000000000000), (19942859217437620089324552351125411881199/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2557/4752)

def qb : ℚ := (427/792)

def rho : ℚ := (291506309374380001156156127519/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (99509328203628252009707765683/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell195Term00
