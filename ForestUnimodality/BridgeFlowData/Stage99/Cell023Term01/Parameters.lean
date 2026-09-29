import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell023Term01
open CoupledFlow


def environment : Environment := ⟨(65/88), (22/29), (612745098039215686274509803921568627451/250000000000000000000000000000000000000), (862745098039215686274509803921568627451/250000000000000000000000000000000000000), 2, (688906673188543200382749909329281924047/625000000000000000000000000000000000000), (2977316416762783544790465205690119184929/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (65/153)

def qb : ℚ := (22/51)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (232179493237273661517595972203/1000000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell023Term01
