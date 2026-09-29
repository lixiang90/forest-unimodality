import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell188Term00
open CoupledFlow


def environment : Environment := ⟨(643/545), (859/725), (27149920690376022258873131301605838955049/10000000000000000000000000000000000000000), (37149920690376022258873131301605838955049/10000000000000000000000000000000000000000), 12, (1965071875802152025895064887319576402759/1250000000000000000000000000000000000000), (5036581735011521957129422315037786562877/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (643/1188)

def qb : ℚ := (859/1584)

def rho : ℚ := (145975541729343808374539033223/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (175070431860804980562561437571/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell188Term00
