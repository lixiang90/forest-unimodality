import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell182Term00
open CoupledFlow


def environment : Environment := ⟨(41/22), (83/43), (7900790514347901633150776914051534676023/2500000000000000000000000000000000000000), (10400790514347901633150776914051534676023/2500000000000000000000000000000000000000), 15, (4165373634370653694028182374262030029107/1250000000000000000000000000000000000000), (27405257545742090017508396313215154860633/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (41/63)

def qb : ℚ := (83/126)

def rho : ℚ := (79168280264543326297845638371/250000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (35384138187026258969862619781/200000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell182Term00
