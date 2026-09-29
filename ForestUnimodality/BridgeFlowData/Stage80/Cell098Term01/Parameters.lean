import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell098Term01
open CoupledFlow


def environment : Environment := ⟨(10787/10225), (53/50), (26395449449004631753448190043839703670561/10000000000000000000000000000000000000000), (36395449449004631753448190043839703670561/10000000000000000000000000000000000000000), 9, (14288577656872702795577190248805636305467/10000000000000000000000000000000000000000), (18727755541720829931385961867218488296503/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (10787/21012)

def qb : ℚ := (53/103)

def rho : ℚ := (282762331327763909315096998313/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (55527420122907919630496575267/200000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell098Term01
