import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell080Term01
open CoupledFlow


def environment : Environment := ⟨(131/133), (197/199), (25973705131981847179809624337536490381843/10000000000000000000000000000000000000000), (35973705131981847179809624337536490381843/10000000000000000000000000000000000000000), 5, (13052310998918844399229593843837877835041/10000000000000000000000000000000000000000), (357920197525273934061742221944176192183/200000000000000000000000000000000000000)⟩

def qa : ℚ := (131/264)

def qb : ℚ := (197/396)

def rho : ℚ := (276576875053370861805482672097/1000000000000000000000000000000)

def retention : ℚ := (2/5)

def rate : ℚ := (231266785486999492894081455131/1000000000000000000000000000000)

def finish : ℚ := (183258146374831/200000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell080Term01
