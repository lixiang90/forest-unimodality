import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell224Term00
open CoupledFlow


def environment : Environment := ⟨(9/5), (41/22), (30850300442292390855352466605592120626319/10000000000000000000000000000000000000000), (40850300442292390855352466605592120626319/10000000000000000000000000000000000000000), 15, (16312211439508064072857063322747318634393/5000000000000000000000000000000000000000), (26585116160856952778880176679829792788557/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (9/14)

def qb : ℚ := (41/63)

def rho : ℚ := (159311839508500391642878952889/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (27911280408640169583763237577/250000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell224Term00
