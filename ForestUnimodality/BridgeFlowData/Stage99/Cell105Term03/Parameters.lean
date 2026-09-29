import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell105Term03
open CoupledFlow


def environment : Environment := ⟨(11311/10425), (22647/20825), (13397161539434796520040856030717727937193/5000000000000000000000000000000000000000), (18397161539434796520040856030717727937193/5000000000000000000000000000000000000000), 9, (3618701309843707999449445332430604808343/2500000000000000000000000000000000000000), (19168224023904114684825417120337890347517/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (11311/21736)

def qb : ℚ := (22647/43472)

def rho : ℚ := (141585976877427842518787667141/500000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (17109350847088562325012354971/62500000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell105Term03
