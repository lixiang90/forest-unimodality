import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell031Term02
open CoupledFlow


def environment : Environment := ⟨(1677/1895), (841/945), (13481587212837969036700582144895606370607/5000000000000000000000000000000000000000), (18481587212837969036700582144895606370607/5000000000000000000000000000000000000000), 3, (498800899973701187253118547228576051603/400000000000000000000000000000000000000), (17405391764833966360431343318989031307593/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (1677/3572)

def qb : ℚ := (841/1786)

def rho : ℚ := (50957166506516712323781477147/200000000000000000000000000000)

def retention : ℚ := (1/1000)

def rate : ℚ := (268785478185706756105751677657/1000000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell031Term02
