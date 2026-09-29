import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell057Term02
open CoupledFlow


def environment : Environment := ⟨(131/133), (197/199), (13112526883092757117943473589002461865659/5000000000000000000000000000000000000000), (18112526883092757117943473589002461865659/5000000000000000000000000000000000000000), 5, (6580525741951070532731507480316392142021/5000000000000000000000000000000000000000), (563157796081009020239088430718668716467/312500000000000000000000000000000000000)⟩

def qa : ℚ := (131/264)

def qb : ℚ := (197/396)

def rho : ℚ := (274657838017686064792003406529/1000000000000000000000000000000)

def retention : ℚ := (1/2)

def rate : ℚ := (102912034891392155156624566093/500000000000000000000000000000)

def finish : ℚ := (6931471805599453/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell057Term02
