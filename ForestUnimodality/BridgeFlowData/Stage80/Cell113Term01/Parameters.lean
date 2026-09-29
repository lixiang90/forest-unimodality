import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell113Term01
open CoupledFlow


def environment : Environment := ⟨(22597/20875), (11311/10425), (26510213539093225469163703820038382692813/10000000000000000000000000000000000000000), (36510213539093225469163703820038382692813/10000000000000000000000000000000000000000), 9, (7171082670813109901360533581568334723203/5000000000000000000000000000000000000000), (4749804763303775686438519666779238896743/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (22597/43472)

def qb : ℚ := (11311/21736)

def rho : ℚ := (285060471803279047008471983071/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (270428553168734166397737514281/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell113Term01
