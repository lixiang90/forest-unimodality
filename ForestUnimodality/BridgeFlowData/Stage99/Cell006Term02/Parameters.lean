import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell006Term02
open CoupledFlow


def environment : Environment := ⟨(37/89), (19/44), (14126984126984126984126984126984126984127/10000000000000000000000000000000000000000), (24126984126984126984126984126984126984127/10000000000000000000000000000000000000000), 0, (310390589107905026640822020225336780543/625000000000000000000000000000000000000), (909549004787100025195263290501385739481/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (37/126)

def qb : ℚ := (19/63)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (5819076203921655548265844447/31250000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell006Term02
