import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell206Term02
open CoupledFlow


def environment : Environment := ⟨(5/4), (116/91), (3479803452261417743742659110334706872619/1250000000000000000000000000000000000000), (4729803452261417743742659110334706872619/1250000000000000000000000000000000000000), 13, (134639795307147373154468841358920521543/78125000000000000000000000000000000000), (21204143013036694039580616687877333226041/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (5/9)

def qb : ℚ := (116/207)

def rho : ℚ := (37024957741770645243848397233/125000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (10307423634724235872265361091/100000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell206Term02
