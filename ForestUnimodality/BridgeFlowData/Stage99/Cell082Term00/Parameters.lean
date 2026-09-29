import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell082Term00
open CoupledFlow


def environment : Environment := ⟨(10787/10225), (53/50), (13295001643355193208423488966482315128561/5000000000000000000000000000000000000000), (18295001643355193208423488966482315128561/5000000000000000000000000000000000000000), 9, (14379419211881090706779460835685531894987/10000000000000000000000000000000000000000), (9413932884444905243169368108966628172949/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (10787/21012)

def qb : ℚ := (53/103)

def rho : ℚ := (281258846993876917482518042061/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (141571090867044978231194595529/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell082Term00
