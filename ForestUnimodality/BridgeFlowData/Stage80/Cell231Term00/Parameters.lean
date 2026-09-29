import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell231Term00
open CoupledFlow


def environment : Environment := ⟨2, (35/17), (3943229480004454512931921210665232984461/1250000000000000000000000000000000000000), (5193229480004454512931921210665232984461/1250000000000000000000000000000000000000), 15, (33269806980205080548974186102987226551461/10000000000000000000000000000000000000000), (27963543353870139685018037288197408377867/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2/3)

def qb : ℚ := (35/52)

def rho : ℚ := (64803310316680415839760176633/200000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (137374183529187119638413591987/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell231Term00
