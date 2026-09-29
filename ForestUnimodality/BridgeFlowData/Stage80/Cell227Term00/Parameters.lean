import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell227Term00
open CoupledFlow


def environment : Environment := ⟨(9/5), (41/22), (30907528430392731350258622837153965875071/10000000000000000000000000000000000000000), (40907528430392731350258622837153965875071/10000000000000000000000000000000000000000), 15, (6535506729795732221319283342714420883883/2000000000000000000000000000000000000000), (13311179886080174486988916954946925403793/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (9/14)

def qb : ℚ := (41/63)

def rho : ℚ := (9943060540510068514055379227/31250000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (6831344296164892988738223113/40000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell227Term00
