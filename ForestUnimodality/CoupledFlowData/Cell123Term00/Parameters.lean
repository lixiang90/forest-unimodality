import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell123Term00
open CoupledFlow


def environment : Environment := ⟨(10787/10225), (53/50), (26345694249643963034490443488577115364353/10000000000000000000000000000000000000000), (36345694249643963034490443488577115364353/10000000000000000000000000000000000000000), 9, (7132671747876849936815121152998233926493/5000000000000000000000000000000000000000), (9351076675879272042854337402400908321897/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (10787/21012)

def qb : ℚ := (53/103)

def rho : ℚ := (283149416963555229276955770059/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (17696537733462881084221267669/125000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell123Term00
