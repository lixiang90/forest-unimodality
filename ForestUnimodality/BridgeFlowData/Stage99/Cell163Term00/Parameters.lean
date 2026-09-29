import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell163Term00
open CoupledFlow


def environment : Environment := ⟨(5/4), (116/91), (14152891462102352466064829448595866858517/5000000000000000000000000000000000000000), (19152891462102352466064829448595866858517/5000000000000000000000000000000000000000), 13, (17484945323188909344977837386327295463447/10000000000000000000000000000000000000000), (21466042604868337063415654261228217928387/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (5/9)

def qb : ℚ := (116/207)

def rho : ℚ := (2340686677157997472288305643/8000000000000000000000000000)

def retention : ℚ := (19/20)

def rate : ℚ := (13727241376557496475778989899/500000000000000000000000000000)

def finish : ℚ := (5129329438755053342619614425468723841/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell163Term00
