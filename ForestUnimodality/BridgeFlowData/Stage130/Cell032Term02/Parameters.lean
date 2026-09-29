import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell032Term02
open CoupledFlow


def environment : Environment := ⟨(841/945), (1687/1885), (27782754759238521836506159014557670772677/10000000000000000000000000000000000000000), (37782754759238521836506159014557670772677/10000000000000000000000000000000000000000), 3, (12797689175141063653008084128278006436711/10000000000000000000000000000000000000000), (8922103482479757326173836822166684013649/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (841/1786)

def qb : ℚ := (1687/3572)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (48923583373527299780038958087/200000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell032Term02
