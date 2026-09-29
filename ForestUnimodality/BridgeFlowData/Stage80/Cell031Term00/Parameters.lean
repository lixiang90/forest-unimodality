import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell031Term00
open CoupledFlow


def environment : Environment := ⟨(1677/1895), (841/945), (202422146759370632648226048152711497459/80000000000000000000000000000000000000), (282422146759370632648226048152711497459/80000000000000000000000000000000000000), 3, (11805530206870205111364733225422124071413/10000000000000000000000000000000000000000), (16623532014601812853944436344934936265609/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (1677/3572)

def qb : ℚ := (841/1786)

def rho : ℚ := (266769253818242794554719300137/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (64924687907894441298221999671/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell031Term00
