import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell024Term02
open CoupledFlow


def environment : Environment := ⟨(22/29), (67/86), (12516339869281045751633986928104575163399/5000000000000000000000000000000000000000), (17516339869281045751633986928104575163399/5000000000000000000000000000000000000000), 2, (11223532305972718766824258364589135967297/10000000000000000000000000000000000000000), (15341108120808236148489897048143876286899/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (22/51)

def qb : ℚ := (67/153)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (47593265870113717229237427469/200000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell024Term02
