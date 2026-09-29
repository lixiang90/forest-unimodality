import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell045Term03
open CoupledFlow


def environment : Environment := ⟨(4487/4825), (8999/9625), (13314006800640485076713060381383404993679/5000000000000000000000000000000000000000), (18314006800640485076713060381383404993679/5000000000000000000000000000000000000000), 4, (6464670795152852864480388397952958563629/5000000000000000000000000000000000000000), (17698426460369815851089006698031492862771/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (4487/9312)

def qb : ℚ := (8999/18624)

def rho : ℚ := (263838347218173096535959736643/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (265026708101900758439298025771/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell045Term03
