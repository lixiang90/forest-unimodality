import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell024Term01
open CoupledFlow


def environment : Environment := ⟨(22/29), (67/86), (12516339869281045751633986928104575163399/5000000000000000000000000000000000000000), (17516339869281045751633986928104575163399/5000000000000000000000000000000000000000), 2, (11223532305972718766824258364589135967297/10000000000000000000000000000000000000000), (15341108120808236148489897048143876286899/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (22/51)

def qb : ℚ := (67/153)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (229822747728841534547645529001/1000000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell024Term01
