import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell023Term00
open CoupledFlow


def environment : Environment := ⟨(65/88), (22/29), (612745098039215686274509803921568627451/250000000000000000000000000000000000000), (862745098039215686274509803921568627451/250000000000000000000000000000000000000), 2, (688906673188543200382749909329281924047/625000000000000000000000000000000000000), (2977316416762783544790465205690119184929/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (65/153)

def qb : ℚ := (22/51)

def rho : ℚ := (1/4)

def retention : ℚ := (9/20)

def rate : ℚ := (179555580327114765162323181941/1000000000000000000000000000000)

def finish : ℚ := (19962692405444290266118327557437234159/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell023Term00
