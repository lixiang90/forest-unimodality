import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell021Term00
open CoupledFlow


def environment : Environment := ⟨(7/10), (64/89), (23464052287581699346405228758169934640523/10000000000000000000000000000000000000000), (33464052287581699346405228758169934640523/10000000000000000000000000000000000000000), 2, (10620133692325742068839013778715747169947/10000000000000000000000000000000000000000), (13998034943825024563202187192959972660089/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (7/17)

def qb : ℚ := (64/153)

def rho : ℚ := (1/4)

def retention : ℚ := (3/20)

def rate : ℚ := (214173027808615080838750353641/1000000000000000000000000000000)

def finish : ℚ := (1897119984885881302039978339220015071/1000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell021Term00
