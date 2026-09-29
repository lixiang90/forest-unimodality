import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell177Term00
open CoupledFlow


def environment : Environment := ⟨(29/25), (2557/2195), (2700576167245563046393260941252294092099/1000000000000000000000000000000000000000), (3700576167245563046393260941252294092099/1000000000000000000000000000000000000000), 12, (15648333309871794793179147599890615110657/10000000000000000000000000000000000000000), (19912401640671095769418283305517920861737/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (29/54)

def qb : ℚ := (2557/4752)

def rho : ℚ := (14540687754300154455099421949/50000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (21457185772644720321925066927/125000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell177Term00
