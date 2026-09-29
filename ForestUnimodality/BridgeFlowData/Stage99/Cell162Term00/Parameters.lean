import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell162Term00
open CoupledFlow


def environment : Environment := ⟨(99/80), (5/4), (1753794235093818638098322646501619873/625000000000000000000000000000000000), (2378794235093818638098322646501619873/625000000000000000000000000000000000), 13, (17353307458333667806318575141220508202147/10000000000000000000000000000000000000000), (4228967529055677578841462482669546440889/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (99/179)

def qb : ℚ := (5/9)

def rho : ℚ := (2335450235079473696115625513/8000000000000000000000000000)

def retention : ℚ := (19/20)

def rate : ℚ := (13654112217119105852913926873/500000000000000000000000000000)

def finish : ℚ := (5129329438755053342619614425468723841/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell162Term00
