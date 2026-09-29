import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell152Term01
open CoupledFlow


def environment : Environment := ⟨(47737/42575), (31833/28375), (1334689084077018602258204110127595050447/500000000000000000000000000000000000000), (1834689084077018602258204110127595050447/500000000000000000000000000000000000000), 10, (14866026344005166835492712803956024999137/10000000000000000000000000000000000000000), (19400630352585614259130152616825582394659/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (47737/90312)

def qb : ℚ := (31833/60208)

def rho : ℚ := (18011127832006968926928552009/62500000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (278195487489029086577184256013/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell152Term01
