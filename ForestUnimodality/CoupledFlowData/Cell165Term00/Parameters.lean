import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell165Term00
open CoupledFlow


def environment : Environment := ⟨(11791/10575), (23607/21125), (5327623698945572681367596133614291405399/2000000000000000000000000000000000000000), (7327623698945572681367596133614291405399/2000000000000000000000000000000000000000), 10, (7419625218181985690297044997845305829277/5000000000000000000000000000000000000000), (604234708447700102447090596239243498807/312500000000000000000000000000000000000)⟩

def qa : ℚ := (11791/22366)

def qb : ℚ := (23607/44732)

def rho : ℚ := (288084118101209636173010121181/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50198462338149975325321192771/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell165Term00
