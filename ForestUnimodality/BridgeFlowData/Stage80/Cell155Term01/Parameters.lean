import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell155Term01
open CoupledFlow


def environment : Environment := ⟨(95549/85075), (15929/14175), (26703864113263957371048923390867804387267/10000000000000000000000000000000000000000), (36703864113263957371048923390867804387267/10000000000000000000000000000000000000000), 10, (1487087621191465266166876909124881244127/1000000000000000000000000000000000000000), (19421201549966169843324418704927360353601/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (95549/180624)

def qb : ℚ := (15929/30104)

def rho : ℚ := (4505080340317436302509002393/15625000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (69631132554487617146304614227/250000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell155Term01
